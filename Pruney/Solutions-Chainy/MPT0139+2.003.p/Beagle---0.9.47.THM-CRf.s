%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:46 EST 2020

% Result     : Theorem 16.00s
% Output     : CNFRefutation 16.00s
% Verified   : 
% Statistics : Number of formulae       :   58 (  68 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   36 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(c_58,plain,(
    ! [A_47,F_52,E_51,D_50,C_49,B_48] : k2_xboole_0(k1_tarski(A_47),k3_enumset1(B_48,C_49,D_50,E_51,F_52)) = k4_enumset1(A_47,B_48,C_49,D_50,E_51,F_52) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,(
    ! [B_43,A_42,D_45,E_46,C_44] : k2_xboole_0(k2_tarski(A_42,B_43),k1_enumset1(C_44,D_45,E_46)) = k3_enumset1(A_42,B_43,C_44,D_45,E_46) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33] : k2_xboole_0(k1_tarski(A_31),k2_tarski(B_32,C_33)) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_196,plain,(
    ! [A_80,B_81,C_82] : k2_xboole_0(k2_xboole_0(A_80,B_81),C_82) = k2_xboole_0(A_80,k2_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4980,plain,(
    ! [A_3398,B_3399,C_3400,C_3401] : k2_xboole_0(k1_tarski(A_3398),k2_xboole_0(k2_tarski(B_3399,C_3400),C_3401)) = k2_xboole_0(k1_enumset1(A_3398,B_3399,C_3400),C_3401) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_196])).

tff(c_5053,plain,(
    ! [B_43,A_42,D_45,A_3398,E_46,C_44] : k2_xboole_0(k1_enumset1(A_3398,A_42,B_43),k1_enumset1(C_44,D_45,E_46)) = k2_xboole_0(k1_tarski(A_3398),k3_enumset1(A_42,B_43,C_44,D_45,E_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4980])).

tff(c_5174,plain,(
    ! [B_43,A_42,D_45,A_3398,E_46,C_44] : k2_xboole_0(k1_enumset1(A_3398,A_42,B_43),k1_enumset1(C_44,D_45,E_46)) = k4_enumset1(A_3398,A_42,B_43,C_44,D_45,E_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5053])).

tff(c_48,plain,(
    ! [A_29,B_30] : k2_xboole_0(k1_tarski(A_29),k1_tarski(B_30)) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [A_66,B_67] : k2_xboole_0(k1_tarski(A_66),k1_tarski(B_67)) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [B_67] : k2_tarski(B_67,B_67) = k1_tarski(B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_2])).

tff(c_149,plain,(
    ! [A_73,B_74,C_75] : k2_xboole_0(k1_tarski(A_73),k2_tarski(B_74,C_75)) = k1_enumset1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,(
    ! [A_73,B_67] : k2_xboole_0(k1_tarski(A_73),k1_tarski(B_67)) = k1_enumset1(A_73,B_67,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_149])).

tff(c_172,plain,(
    ! [A_73,B_67] : k1_enumset1(A_73,B_67,B_67) = k2_tarski(A_73,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_168])).

tff(c_1092,plain,(
    ! [A_1239,B_1240,C_1241,D_1242] : k2_xboole_0(k1_tarski(A_1239),k1_enumset1(B_1240,C_1241,D_1242)) = k2_enumset1(A_1239,B_1240,C_1241,D_1242) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1182,plain,(
    ! [A_1239,A_73,B_67] : k2_xboole_0(k1_tarski(A_1239),k2_tarski(A_73,B_67)) = k2_enumset1(A_1239,A_73,B_67,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_1092])).

tff(c_1191,plain,(
    ! [A_1239,A_73,B_67] : k2_enumset1(A_1239,A_73,B_67,B_67) = k1_enumset1(A_1239,A_73,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1182])).

tff(c_1346,plain,(
    ! [A_1501,B_1502,C_1503,D_1504] : k2_xboole_0(k2_tarski(A_1501,B_1502),k2_tarski(C_1503,D_1504)) = k2_enumset1(A_1501,B_1502,C_1503,D_1504) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1374,plain,(
    ! [A_1501,B_1502,B_67] : k2_xboole_0(k2_tarski(A_1501,B_1502),k1_tarski(B_67)) = k2_enumset1(A_1501,B_1502,B_67,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1346])).

tff(c_1385,plain,(
    ! [A_1501,B_1502,B_67] : k2_xboole_0(k2_tarski(A_1501,B_1502),k1_tarski(B_67)) = k1_enumset1(A_1501,B_1502,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_1374])).

tff(c_2494,plain,(
    ! [D_2218,B_2215,A_2217,E_2216,C_2214] : k2_xboole_0(k1_enumset1(A_2217,B_2215,C_2214),k2_tarski(D_2218,E_2216)) = k3_enumset1(A_2217,B_2215,C_2214,D_2218,E_2216) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30275,plain,(
    ! [A_9742,C_9743,D_9741,B_9744,E_9746,C_9745] : k2_xboole_0(k1_enumset1(A_9742,B_9744,C_9743),k2_xboole_0(k2_tarski(D_9741,E_9746),C_9745)) = k2_xboole_0(k3_enumset1(A_9742,B_9744,C_9743,D_9741,E_9746),C_9745) ),
    inference(superposition,[status(thm),theory(equality)],[c_2494,c_4])).

tff(c_30523,plain,(
    ! [A_9742,C_9743,B_67,B_9744,B_1502,A_1501] : k2_xboole_0(k3_enumset1(A_9742,B_9744,C_9743,A_1501,B_1502),k1_tarski(B_67)) = k2_xboole_0(k1_enumset1(A_9742,B_9744,C_9743),k1_enumset1(A_1501,B_1502,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1385,c_30275])).

tff(c_30616,plain,(
    ! [A_9742,C_9743,B_67,B_9744,B_1502,A_1501] : k2_xboole_0(k3_enumset1(A_9742,B_9744,C_9743,A_1501,B_1502),k1_tarski(B_67)) = k4_enumset1(A_9742,B_9744,C_9743,A_1501,B_1502,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5174,c_30523])).

tff(c_60,plain,(
    k2_xboole_0(k3_enumset1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k1_tarski('#skF_10')) != k4_enumset1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30616,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.00/8.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.00/8.04  
% 16.00/8.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.00/8.04  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4
% 16.00/8.04  
% 16.00/8.04  %Foreground sorts:
% 16.00/8.04  
% 16.00/8.04  
% 16.00/8.04  %Background operators:
% 16.00/8.04  
% 16.00/8.04  
% 16.00/8.04  %Foreground operators:
% 16.00/8.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.00/8.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.00/8.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.00/8.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.00/8.04  tff('#skF_7', type, '#skF_7': $i).
% 16.00/8.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.00/8.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.00/8.04  tff('#skF_10', type, '#skF_10': $i).
% 16.00/8.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.00/8.04  tff('#skF_5', type, '#skF_5': $i).
% 16.00/8.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 16.00/8.04  tff('#skF_6', type, '#skF_6': $i).
% 16.00/8.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.00/8.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.00/8.04  tff('#skF_9', type, '#skF_9': $i).
% 16.00/8.04  tff('#skF_8', type, '#skF_8': $i).
% 16.00/8.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.00/8.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.00/8.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.00/8.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 16.00/8.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.00/8.04  
% 16.00/8.06  tff(f_69, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 16.00/8.06  tff(f_67, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 16.00/8.06  tff(f_61, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 16.00/8.06  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 16.00/8.06  tff(f_59, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 16.00/8.06  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 16.00/8.06  tff(f_63, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 16.00/8.06  tff(f_55, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 16.00/8.06  tff(f_57, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 16.00/8.06  tff(f_72, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 16.00/8.06  tff(c_58, plain, (![A_47, F_52, E_51, D_50, C_49, B_48]: (k2_xboole_0(k1_tarski(A_47), k3_enumset1(B_48, C_49, D_50, E_51, F_52))=k4_enumset1(A_47, B_48, C_49, D_50, E_51, F_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.00/8.06  tff(c_56, plain, (![B_43, A_42, D_45, E_46, C_44]: (k2_xboole_0(k2_tarski(A_42, B_43), k1_enumset1(C_44, D_45, E_46))=k3_enumset1(A_42, B_43, C_44, D_45, E_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.00/8.06  tff(c_50, plain, (![A_31, B_32, C_33]: (k2_xboole_0(k1_tarski(A_31), k2_tarski(B_32, C_33))=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.00/8.06  tff(c_196, plain, (![A_80, B_81, C_82]: (k2_xboole_0(k2_xboole_0(A_80, B_81), C_82)=k2_xboole_0(A_80, k2_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.00/8.06  tff(c_4980, plain, (![A_3398, B_3399, C_3400, C_3401]: (k2_xboole_0(k1_tarski(A_3398), k2_xboole_0(k2_tarski(B_3399, C_3400), C_3401))=k2_xboole_0(k1_enumset1(A_3398, B_3399, C_3400), C_3401))), inference(superposition, [status(thm), theory('equality')], [c_50, c_196])).
% 16.00/8.06  tff(c_5053, plain, (![B_43, A_42, D_45, A_3398, E_46, C_44]: (k2_xboole_0(k1_enumset1(A_3398, A_42, B_43), k1_enumset1(C_44, D_45, E_46))=k2_xboole_0(k1_tarski(A_3398), k3_enumset1(A_42, B_43, C_44, D_45, E_46)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4980])).
% 16.00/8.06  tff(c_5174, plain, (![B_43, A_42, D_45, A_3398, E_46, C_44]: (k2_xboole_0(k1_enumset1(A_3398, A_42, B_43), k1_enumset1(C_44, D_45, E_46))=k4_enumset1(A_3398, A_42, B_43, C_44, D_45, E_46))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5053])).
% 16.00/8.06  tff(c_48, plain, (![A_29, B_30]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(B_30))=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.00/8.06  tff(c_80, plain, (![A_66, B_67]: (k2_xboole_0(k1_tarski(A_66), k1_tarski(B_67))=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.00/8.06  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.00/8.06  tff(c_87, plain, (![B_67]: (k2_tarski(B_67, B_67)=k1_tarski(B_67))), inference(superposition, [status(thm), theory('equality')], [c_80, c_2])).
% 16.00/8.06  tff(c_149, plain, (![A_73, B_74, C_75]: (k2_xboole_0(k1_tarski(A_73), k2_tarski(B_74, C_75))=k1_enumset1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.00/8.06  tff(c_168, plain, (![A_73, B_67]: (k2_xboole_0(k1_tarski(A_73), k1_tarski(B_67))=k1_enumset1(A_73, B_67, B_67))), inference(superposition, [status(thm), theory('equality')], [c_87, c_149])).
% 16.00/8.06  tff(c_172, plain, (![A_73, B_67]: (k1_enumset1(A_73, B_67, B_67)=k2_tarski(A_73, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_168])).
% 16.00/8.06  tff(c_1092, plain, (![A_1239, B_1240, C_1241, D_1242]: (k2_xboole_0(k1_tarski(A_1239), k1_enumset1(B_1240, C_1241, D_1242))=k2_enumset1(A_1239, B_1240, C_1241, D_1242))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.00/8.06  tff(c_1182, plain, (![A_1239, A_73, B_67]: (k2_xboole_0(k1_tarski(A_1239), k2_tarski(A_73, B_67))=k2_enumset1(A_1239, A_73, B_67, B_67))), inference(superposition, [status(thm), theory('equality')], [c_172, c_1092])).
% 16.00/8.06  tff(c_1191, plain, (![A_1239, A_73, B_67]: (k2_enumset1(A_1239, A_73, B_67, B_67)=k1_enumset1(A_1239, A_73, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1182])).
% 16.00/8.06  tff(c_1346, plain, (![A_1501, B_1502, C_1503, D_1504]: (k2_xboole_0(k2_tarski(A_1501, B_1502), k2_tarski(C_1503, D_1504))=k2_enumset1(A_1501, B_1502, C_1503, D_1504))), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.00/8.06  tff(c_1374, plain, (![A_1501, B_1502, B_67]: (k2_xboole_0(k2_tarski(A_1501, B_1502), k1_tarski(B_67))=k2_enumset1(A_1501, B_1502, B_67, B_67))), inference(superposition, [status(thm), theory('equality')], [c_87, c_1346])).
% 16.00/8.06  tff(c_1385, plain, (![A_1501, B_1502, B_67]: (k2_xboole_0(k2_tarski(A_1501, B_1502), k1_tarski(B_67))=k1_enumset1(A_1501, B_1502, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_1374])).
% 16.00/8.06  tff(c_2494, plain, (![D_2218, B_2215, A_2217, E_2216, C_2214]: (k2_xboole_0(k1_enumset1(A_2217, B_2215, C_2214), k2_tarski(D_2218, E_2216))=k3_enumset1(A_2217, B_2215, C_2214, D_2218, E_2216))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.00/8.06  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.00/8.06  tff(c_30275, plain, (![A_9742, C_9743, D_9741, B_9744, E_9746, C_9745]: (k2_xboole_0(k1_enumset1(A_9742, B_9744, C_9743), k2_xboole_0(k2_tarski(D_9741, E_9746), C_9745))=k2_xboole_0(k3_enumset1(A_9742, B_9744, C_9743, D_9741, E_9746), C_9745))), inference(superposition, [status(thm), theory('equality')], [c_2494, c_4])).
% 16.00/8.06  tff(c_30523, plain, (![A_9742, C_9743, B_67, B_9744, B_1502, A_1501]: (k2_xboole_0(k3_enumset1(A_9742, B_9744, C_9743, A_1501, B_1502), k1_tarski(B_67))=k2_xboole_0(k1_enumset1(A_9742, B_9744, C_9743), k1_enumset1(A_1501, B_1502, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_1385, c_30275])).
% 16.00/8.06  tff(c_30616, plain, (![A_9742, C_9743, B_67, B_9744, B_1502, A_1501]: (k2_xboole_0(k3_enumset1(A_9742, B_9744, C_9743, A_1501, B_1502), k1_tarski(B_67))=k4_enumset1(A_9742, B_9744, C_9743, A_1501, B_1502, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_5174, c_30523])).
% 16.00/8.06  tff(c_60, plain, (k2_xboole_0(k3_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k1_tarski('#skF_10'))!=k4_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.00/8.06  tff(c_30803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30616, c_60])).
% 16.00/8.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.00/8.06  
% 16.00/8.06  Inference rules
% 16.00/8.06  ----------------------
% 16.00/8.06  #Ref     : 0
% 16.00/8.06  #Sup     : 6505
% 16.00/8.06  #Fact    : 0
% 16.00/8.06  #Define  : 0
% 16.00/8.06  #Split   : 10
% 16.00/8.06  #Chain   : 0
% 16.00/8.06  #Close   : 0
% 16.00/8.06  
% 16.00/8.06  Ordering : KBO
% 16.00/8.06  
% 16.00/8.06  Simplification rules
% 16.00/8.06  ----------------------
% 16.00/8.06  #Subsume      : 529
% 16.00/8.06  #Demod        : 13952
% 16.00/8.06  #Tautology    : 3581
% 16.00/8.06  #SimpNegUnit  : 0
% 16.00/8.06  #BackRed      : 1
% 16.00/8.06  
% 16.00/8.06  #Partial instantiations: 4386
% 16.00/8.06  #Strategies tried      : 1
% 16.00/8.06  
% 16.00/8.06  Timing (in seconds)
% 16.00/8.06  ----------------------
% 16.00/8.06  Preprocessing        : 0.33
% 16.00/8.06  Parsing              : 0.18
% 16.00/8.06  CNF conversion       : 0.03
% 16.00/8.06  Main loop            : 6.97
% 16.00/8.06  Inferencing          : 1.36
% 16.00/8.06  Reduction            : 4.58
% 16.00/8.06  Demodulation         : 4.26
% 16.00/8.06  BG Simplification    : 0.14
% 16.00/8.06  Subsumption          : 0.70
% 16.00/8.06  Abstraction          : 0.29
% 16.00/8.06  MUC search           : 0.00
% 16.00/8.06  Cooper               : 0.00
% 16.00/8.06  Total                : 7.32
% 16.00/8.06  Index Insertion      : 0.00
% 16.00/8.06  Index Deletion       : 0.00
% 16.00/8.06  Index Matching       : 0.00
% 16.00/8.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
