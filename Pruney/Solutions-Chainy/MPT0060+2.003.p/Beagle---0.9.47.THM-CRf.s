%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:05 EST 2020

% Result     : Theorem 13.36s
% Output     : CNFRefutation 13.46s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 182 expanded)
%              Number of leaves         :   19 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :   65 ( 186 expanded)
%              Number of equality atoms :   51 ( 149 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_177,plain,(
    ! [A_38,B_39] : k4_xboole_0(k2_xboole_0(A_38,B_39),B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_568,plain,(
    ! [A_56,B_57] : k4_xboole_0(k4_xboole_0(A_56,B_57),A_56) = k4_xboole_0(A_56,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_177])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_586,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k2_xboole_0(B_57,A_56)) = k4_xboole_0(A_56,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_12])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k4_xboole_0(A_42,B_43),C_44) = k4_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_274,plain,(
    ! [A_9,B_10,C_44] : k4_xboole_0(k2_xboole_0(A_9,B_10),k2_xboole_0(B_10,C_44)) = k4_xboole_0(k4_xboole_0(A_9,B_10),C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_240])).

tff(c_287,plain,(
    ! [A_9,B_10,C_44] : k4_xboole_0(k2_xboole_0(A_9,B_10),k2_xboole_0(B_10,C_44)) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_274])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_913,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k2_xboole_0(B_72,A_71)) = k4_xboole_0(A_71,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_12])).

tff(c_1004,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_913])).

tff(c_292,plain,(
    ! [A_45,B_46] : r1_tarski(k4_xboole_0(A_45,B_46),k2_xboole_0(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10890,plain,(
    ! [A_261,B_262] : k2_xboole_0(k4_xboole_0(A_261,B_262),k2_xboole_0(A_261,B_262)) = k2_xboole_0(A_261,B_262) ),
    inference(resolution,[status(thm)],[c_292,c_4])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_277,plain,(
    ! [A_14,B_15,C_44] : k4_xboole_0(A_14,k2_xboole_0(k4_xboole_0(A_14,B_15),C_44)) = k4_xboole_0(k3_xboole_0(A_14,B_15),C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_240])).

tff(c_4005,plain,(
    ! [A_14,B_15,C_44] : k4_xboole_0(A_14,k2_xboole_0(k4_xboole_0(A_14,B_15),C_44)) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_277])).

tff(c_10953,plain,(
    ! [A_261,B_262] : k3_xboole_0(A_261,k4_xboole_0(B_262,k2_xboole_0(A_261,B_262))) = k4_xboole_0(A_261,k2_xboole_0(A_261,B_262)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10890,c_4005])).

tff(c_11182,plain,(
    ! [A_261,B_262] : k4_xboole_0(A_261,A_261) = k3_xboole_0(A_261,k4_xboole_0(B_262,B_262)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_586,c_10953])).

tff(c_183,plain,(
    ! [A_38,B_39] : k4_xboole_0(k2_xboole_0(A_38,B_39),k4_xboole_0(A_38,B_39)) = k3_xboole_0(k2_xboole_0(A_38,B_39),B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_14])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5216,plain,(
    ! [A_170,B_171] : k4_xboole_0(k2_xboole_0(A_170,B_171),k4_xboole_0(B_171,A_170)) = k4_xboole_0(A_170,k4_xboole_0(B_171,A_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_177])).

tff(c_5431,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k4_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5216])).

tff(c_14134,plain,(
    ! [B_305,A_306] : k4_xboole_0(B_305,k4_xboole_0(A_306,B_305)) = k3_xboole_0(k2_xboole_0(A_306,B_305),B_305) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_5431])).

tff(c_59,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),A_25) = A_25 ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_65,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_2])).

tff(c_14934,plain,(
    ! [B_313,A_314] : k2_xboole_0(B_313,k3_xboole_0(k2_xboole_0(A_314,B_313),B_313)) = B_313 ),
    inference(superposition,[status(thm),theory(equality)],[c_14134,c_65])).

tff(c_2202,plain,(
    ! [A_105,B_106,C_107] : k4_xboole_0(k2_xboole_0(A_105,B_106),k2_xboole_0(B_106,C_107)) = k4_xboole_0(A_105,k2_xboole_0(B_106,C_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_274])).

tff(c_2517,plain,(
    ! [A_110,B_111,C_112] : r1_tarski(k4_xboole_0(A_110,k2_xboole_0(B_111,C_112)),k2_xboole_0(A_110,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2202,c_6])).

tff(c_2619,plain,(
    ! [A_1,B_2,C_112] : r1_tarski(k4_xboole_0(A_1,k2_xboole_0(B_2,C_112)),k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2517])).

tff(c_15061,plain,(
    ! [A_314,B_313,C_112] : r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(A_314,B_313),B_313),k2_xboole_0(B_313,C_112)),B_313) ),
    inference(superposition,[status(thm),theory(equality)],[c_14934,c_2619])).

tff(c_16670,plain,(
    ! [A_327,B_328] : r1_tarski(k3_xboole_0(k2_xboole_0(A_327,B_328),k4_xboole_0(B_328,B_328)),B_328) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_16,c_15061])).

tff(c_18044,plain,(
    ! [A_340,B_341] : r1_tarski(k4_xboole_0(k2_xboole_0(A_340,B_341),k2_xboole_0(A_340,B_341)),B_341) ),
    inference(superposition,[status(thm),theory(equality)],[c_11182,c_16670])).

tff(c_18217,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(k2_xboole_0(A_1,B_2),k2_xboole_0(B_2,A_1)),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_18044])).

tff(c_18296,plain,(
    ! [A_342,B_343] : r1_tarski(k4_xboole_0(A_342,A_342),B_343) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_287,c_18217])).

tff(c_18323,plain,(
    ! [A_344,B_345] : k2_xboole_0(k4_xboole_0(A_344,A_344),B_345) = B_345 ),
    inference(resolution,[status(thm)],[c_18296,c_4])).

tff(c_18467,plain,(
    ! [A_344,B_345] : k3_xboole_0(A_344,k4_xboole_0(A_344,B_345)) = k4_xboole_0(A_344,B_345) ),
    inference(superposition,[status(thm),theory(equality)],[c_18323,c_4005])).

tff(c_4006,plain,(
    ! [A_147,B_148,C_149] : k4_xboole_0(A_147,k2_xboole_0(k4_xboole_0(A_147,B_148),C_149)) = k3_xboole_0(A_147,k4_xboole_0(B_148,C_149)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_277])).

tff(c_4225,plain,(
    ! [A_147,B_2,B_148] : k4_xboole_0(A_147,k2_xboole_0(B_2,k4_xboole_0(A_147,B_148))) = k3_xboole_0(A_147,k4_xboole_0(B_148,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4006])).

tff(c_256,plain,(
    ! [C_44,A_42,B_43] : k2_xboole_0(C_44,k4_xboole_0(A_42,k2_xboole_0(B_43,C_44))) = k2_xboole_0(C_44,k4_xboole_0(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_8])).

tff(c_281,plain,(
    ! [A_42,B_43,B_15] : k4_xboole_0(A_42,k2_xboole_0(B_43,k4_xboole_0(k4_xboole_0(A_42,B_43),B_15))) = k3_xboole_0(k4_xboole_0(A_42,B_43),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_240])).

tff(c_8269,plain,(
    ! [A_222,B_223,B_224] : k4_xboole_0(A_222,k2_xboole_0(B_223,k4_xboole_0(A_222,k2_xboole_0(B_223,B_224)))) = k3_xboole_0(k4_xboole_0(A_222,B_223),B_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_281])).

tff(c_8589,plain,(
    ! [A_222,B_2,A_1] : k4_xboole_0(A_222,k2_xboole_0(B_2,k4_xboole_0(A_222,k2_xboole_0(A_1,B_2)))) = k3_xboole_0(k4_xboole_0(A_222,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8269])).

tff(c_8641,plain,(
    ! [A_222,B_2,A_1] : k4_xboole_0(A_222,k2_xboole_0(B_2,k4_xboole_0(A_222,A_1))) = k3_xboole_0(k4_xboole_0(A_222,B_2),A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8589])).

tff(c_42120,plain,(
    ! [A_222,B_2,A_1] : k3_xboole_0(k4_xboole_0(A_222,B_2),A_1) = k3_xboole_0(A_222,k4_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4225,c_8641])).

tff(c_18,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_42134,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42120,c_19])).

tff(c_42147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18467,c_12,c_42134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n003.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 09:28:27 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.36/6.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.36/6.12  
% 13.36/6.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.36/6.12  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 13.36/6.12  
% 13.36/6.12  %Foreground sorts:
% 13.36/6.12  
% 13.36/6.12  
% 13.36/6.12  %Background operators:
% 13.36/6.12  
% 13.36/6.12  
% 13.36/6.12  %Foreground operators:
% 13.36/6.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.36/6.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.36/6.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.36/6.12  tff('#skF_2', type, '#skF_2': $i).
% 13.36/6.12  tff('#skF_3', type, '#skF_3': $i).
% 13.36/6.12  tff('#skF_1', type, '#skF_1': $i).
% 13.36/6.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.36/6.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.36/6.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.36/6.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.36/6.12  
% 13.46/6.14  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.46/6.14  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.46/6.14  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 13.46/6.14  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 13.46/6.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.46/6.14  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 13.46/6.14  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.46/6.14  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.46/6.14  tff(f_46, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 13.46/6.14  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.46/6.14  tff(c_54, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.46/6.14  tff(c_58, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_54])).
% 13.46/6.14  tff(c_177, plain, (![A_38, B_39]: (k4_xboole_0(k2_xboole_0(A_38, B_39), B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.46/6.14  tff(c_568, plain, (![A_56, B_57]: (k4_xboole_0(k4_xboole_0(A_56, B_57), A_56)=k4_xboole_0(A_56, A_56))), inference(superposition, [status(thm), theory('equality')], [c_58, c_177])).
% 13.46/6.14  tff(c_12, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.46/6.14  tff(c_586, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k2_xboole_0(B_57, A_56))=k4_xboole_0(A_56, A_56))), inference(superposition, [status(thm), theory('equality')], [c_568, c_12])).
% 13.46/6.14  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.46/6.14  tff(c_240, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k4_xboole_0(A_42, B_43), C_44)=k4_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.46/6.14  tff(c_274, plain, (![A_9, B_10, C_44]: (k4_xboole_0(k2_xboole_0(A_9, B_10), k2_xboole_0(B_10, C_44))=k4_xboole_0(k4_xboole_0(A_9, B_10), C_44))), inference(superposition, [status(thm), theory('equality')], [c_10, c_240])).
% 13.46/6.14  tff(c_287, plain, (![A_9, B_10, C_44]: (k4_xboole_0(k2_xboole_0(A_9, B_10), k2_xboole_0(B_10, C_44))=k4_xboole_0(A_9, k2_xboole_0(B_10, C_44)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_274])).
% 13.46/6.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.46/6.14  tff(c_913, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k2_xboole_0(B_72, A_71))=k4_xboole_0(A_71, A_71))), inference(superposition, [status(thm), theory('equality')], [c_568, c_12])).
% 13.46/6.14  tff(c_1004, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_913])).
% 13.46/6.14  tff(c_292, plain, (![A_45, B_46]: (r1_tarski(k4_xboole_0(A_45, B_46), k2_xboole_0(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_177, c_6])).
% 13.46/6.14  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.46/6.14  tff(c_10890, plain, (![A_261, B_262]: (k2_xboole_0(k4_xboole_0(A_261, B_262), k2_xboole_0(A_261, B_262))=k2_xboole_0(A_261, B_262))), inference(resolution, [status(thm)], [c_292, c_4])).
% 13.46/6.14  tff(c_16, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.46/6.14  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.46/6.14  tff(c_277, plain, (![A_14, B_15, C_44]: (k4_xboole_0(A_14, k2_xboole_0(k4_xboole_0(A_14, B_15), C_44))=k4_xboole_0(k3_xboole_0(A_14, B_15), C_44))), inference(superposition, [status(thm), theory('equality')], [c_14, c_240])).
% 13.46/6.14  tff(c_4005, plain, (![A_14, B_15, C_44]: (k4_xboole_0(A_14, k2_xboole_0(k4_xboole_0(A_14, B_15), C_44))=k3_xboole_0(A_14, k4_xboole_0(B_15, C_44)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_277])).
% 13.46/6.14  tff(c_10953, plain, (![A_261, B_262]: (k3_xboole_0(A_261, k4_xboole_0(B_262, k2_xboole_0(A_261, B_262)))=k4_xboole_0(A_261, k2_xboole_0(A_261, B_262)))), inference(superposition, [status(thm), theory('equality')], [c_10890, c_4005])).
% 13.46/6.14  tff(c_11182, plain, (![A_261, B_262]: (k4_xboole_0(A_261, A_261)=k3_xboole_0(A_261, k4_xboole_0(B_262, B_262)))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_586, c_10953])).
% 13.46/6.14  tff(c_183, plain, (![A_38, B_39]: (k4_xboole_0(k2_xboole_0(A_38, B_39), k4_xboole_0(A_38, B_39))=k3_xboole_0(k2_xboole_0(A_38, B_39), B_39))), inference(superposition, [status(thm), theory('equality')], [c_177, c_14])).
% 13.46/6.14  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.46/6.14  tff(c_5216, plain, (![A_170, B_171]: (k4_xboole_0(k2_xboole_0(A_170, B_171), k4_xboole_0(B_171, A_170))=k4_xboole_0(A_170, k4_xboole_0(B_171, A_170)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_177])).
% 13.46/6.14  tff(c_5431, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k4_xboole_0(A_1, B_2))=k4_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5216])).
% 13.46/6.14  tff(c_14134, plain, (![B_305, A_306]: (k4_xboole_0(B_305, k4_xboole_0(A_306, B_305))=k3_xboole_0(k2_xboole_0(A_306, B_305), B_305))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_5431])).
% 13.46/6.14  tff(c_59, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), A_25)=A_25)), inference(resolution, [status(thm)], [c_6, c_54])).
% 13.46/6.14  tff(c_65, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(A_25, B_26))=A_25)), inference(superposition, [status(thm), theory('equality')], [c_59, c_2])).
% 13.46/6.14  tff(c_14934, plain, (![B_313, A_314]: (k2_xboole_0(B_313, k3_xboole_0(k2_xboole_0(A_314, B_313), B_313))=B_313)), inference(superposition, [status(thm), theory('equality')], [c_14134, c_65])).
% 13.46/6.14  tff(c_2202, plain, (![A_105, B_106, C_107]: (k4_xboole_0(k2_xboole_0(A_105, B_106), k2_xboole_0(B_106, C_107))=k4_xboole_0(A_105, k2_xboole_0(B_106, C_107)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_274])).
% 13.46/6.14  tff(c_2517, plain, (![A_110, B_111, C_112]: (r1_tarski(k4_xboole_0(A_110, k2_xboole_0(B_111, C_112)), k2_xboole_0(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_2202, c_6])).
% 13.46/6.14  tff(c_2619, plain, (![A_1, B_2, C_112]: (r1_tarski(k4_xboole_0(A_1, k2_xboole_0(B_2, C_112)), k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2517])).
% 13.46/6.14  tff(c_15061, plain, (![A_314, B_313, C_112]: (r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(A_314, B_313), B_313), k2_xboole_0(B_313, C_112)), B_313))), inference(superposition, [status(thm), theory('equality')], [c_14934, c_2619])).
% 13.46/6.14  tff(c_16670, plain, (![A_327, B_328]: (r1_tarski(k3_xboole_0(k2_xboole_0(A_327, B_328), k4_xboole_0(B_328, B_328)), B_328))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_16, c_15061])).
% 13.46/6.14  tff(c_18044, plain, (![A_340, B_341]: (r1_tarski(k4_xboole_0(k2_xboole_0(A_340, B_341), k2_xboole_0(A_340, B_341)), B_341))), inference(superposition, [status(thm), theory('equality')], [c_11182, c_16670])).
% 13.46/6.14  tff(c_18217, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(k2_xboole_0(A_1, B_2), k2_xboole_0(B_2, A_1)), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_18044])).
% 13.46/6.14  tff(c_18296, plain, (![A_342, B_343]: (r1_tarski(k4_xboole_0(A_342, A_342), B_343))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_287, c_18217])).
% 13.46/6.14  tff(c_18323, plain, (![A_344, B_345]: (k2_xboole_0(k4_xboole_0(A_344, A_344), B_345)=B_345)), inference(resolution, [status(thm)], [c_18296, c_4])).
% 13.46/6.14  tff(c_18467, plain, (![A_344, B_345]: (k3_xboole_0(A_344, k4_xboole_0(A_344, B_345))=k4_xboole_0(A_344, B_345))), inference(superposition, [status(thm), theory('equality')], [c_18323, c_4005])).
% 13.46/6.14  tff(c_4006, plain, (![A_147, B_148, C_149]: (k4_xboole_0(A_147, k2_xboole_0(k4_xboole_0(A_147, B_148), C_149))=k3_xboole_0(A_147, k4_xboole_0(B_148, C_149)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_277])).
% 13.46/6.14  tff(c_4225, plain, (![A_147, B_2, B_148]: (k4_xboole_0(A_147, k2_xboole_0(B_2, k4_xboole_0(A_147, B_148)))=k3_xboole_0(A_147, k4_xboole_0(B_148, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4006])).
% 13.46/6.14  tff(c_256, plain, (![C_44, A_42, B_43]: (k2_xboole_0(C_44, k4_xboole_0(A_42, k2_xboole_0(B_43, C_44)))=k2_xboole_0(C_44, k4_xboole_0(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_240, c_8])).
% 13.46/6.14  tff(c_281, plain, (![A_42, B_43, B_15]: (k4_xboole_0(A_42, k2_xboole_0(B_43, k4_xboole_0(k4_xboole_0(A_42, B_43), B_15)))=k3_xboole_0(k4_xboole_0(A_42, B_43), B_15))), inference(superposition, [status(thm), theory('equality')], [c_14, c_240])).
% 13.46/6.14  tff(c_8269, plain, (![A_222, B_223, B_224]: (k4_xboole_0(A_222, k2_xboole_0(B_223, k4_xboole_0(A_222, k2_xboole_0(B_223, B_224))))=k3_xboole_0(k4_xboole_0(A_222, B_223), B_224))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_281])).
% 13.46/6.14  tff(c_8589, plain, (![A_222, B_2, A_1]: (k4_xboole_0(A_222, k2_xboole_0(B_2, k4_xboole_0(A_222, k2_xboole_0(A_1, B_2))))=k3_xboole_0(k4_xboole_0(A_222, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8269])).
% 13.46/6.14  tff(c_8641, plain, (![A_222, B_2, A_1]: (k4_xboole_0(A_222, k2_xboole_0(B_2, k4_xboole_0(A_222, A_1)))=k3_xboole_0(k4_xboole_0(A_222, B_2), A_1))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_8589])).
% 13.46/6.14  tff(c_42120, plain, (![A_222, B_2, A_1]: (k3_xboole_0(k4_xboole_0(A_222, B_2), A_1)=k3_xboole_0(A_222, k4_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_4225, c_8641])).
% 13.46/6.14  tff(c_18, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.46/6.14  tff(c_19, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 13.46/6.14  tff(c_42134, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42120, c_19])).
% 13.46/6.14  tff(c_42147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18467, c_12, c_42134])).
% 13.46/6.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.46/6.14  
% 13.46/6.14  Inference rules
% 13.46/6.14  ----------------------
% 13.46/6.14  #Ref     : 0
% 13.46/6.14  #Sup     : 10772
% 13.46/6.14  #Fact    : 0
% 13.46/6.14  #Define  : 0
% 13.46/6.14  #Split   : 0
% 13.46/6.14  #Chain   : 0
% 13.46/6.14  #Close   : 0
% 13.46/6.14  
% 13.46/6.14  Ordering : KBO
% 13.46/6.14  
% 13.46/6.14  Simplification rules
% 13.46/6.14  ----------------------
% 13.46/6.14  #Subsume      : 459
% 13.46/6.14  #Demod        : 12210
% 13.46/6.14  #Tautology    : 5927
% 13.46/6.14  #SimpNegUnit  : 0
% 13.46/6.14  #BackRed      : 33
% 13.46/6.14  
% 13.46/6.14  #Partial instantiations: 0
% 13.46/6.14  #Strategies tried      : 1
% 13.46/6.14  
% 13.46/6.14  Timing (in seconds)
% 13.46/6.14  ----------------------
% 13.46/6.14  Preprocessing        : 0.33
% 13.46/6.14  Parsing              : 0.19
% 13.46/6.14  CNF conversion       : 0.02
% 13.46/6.14  Main loop            : 5.11
% 13.46/6.14  Inferencing          : 0.85
% 13.46/6.14  Reduction            : 3.01
% 13.46/6.14  Demodulation         : 2.71
% 13.46/6.14  BG Simplification    : 0.13
% 13.46/6.14  Subsumption          : 0.86
% 13.46/6.14  Abstraction          : 0.22
% 13.46/6.14  MUC search           : 0.00
% 13.46/6.14  Cooper               : 0.00
% 13.46/6.14  Total                : 5.48
% 13.46/6.14  Index Insertion      : 0.00
% 13.46/6.14  Index Deletion       : 0.00
% 13.46/6.14  Index Matching       : 0.00
% 13.46/6.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
