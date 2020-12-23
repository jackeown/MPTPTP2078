%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:01 EST 2020

% Result     : Timeout 58.25s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   67 ( 154 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   57 ( 144 expanded)
%              Number of equality atoms :   56 ( 143 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_350,plain,(
    ! [A_41,B_42,C_43] : k5_xboole_0(k5_xboole_0(A_41,B_42),C_43) = k5_xboole_0(A_41,k5_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_406,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k5_xboole_0(B_42,k5_xboole_0(A_41,B_42))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_350])).

tff(c_104,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [A_28] : k3_xboole_0(k1_xboole_0,A_28) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_10])).

tff(c_275,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k3_xboole_0(A_36,B_37),C_38) = k3_xboole_0(A_36,k4_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_290,plain,(
    ! [A_28,C_38] : k3_xboole_0(k1_xboole_0,k4_xboole_0(A_28,C_38)) = k4_xboole_0(k1_xboole_0,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_275])).

tff(c_328,plain,(
    ! [C_40] : k4_xboole_0(k1_xboole_0,C_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_290])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_337,plain,(
    ! [C_40] : k5_xboole_0(C_40,k1_xboole_0) = k2_xboole_0(C_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_20])).

tff(c_413,plain,(
    ! [C_44] : k2_xboole_0(C_44,k1_xboole_0) = C_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_337])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_425,plain,(
    ! [C_44] : k2_xboole_0(k1_xboole_0,C_44) = C_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_2])).

tff(c_244,plain,(
    ! [A_34,B_35] : k5_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_268,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_244])).

tff(c_306,plain,(
    ! [A_39] : k4_xboole_0(A_39,k1_xboole_0) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_268])).

tff(c_316,plain,(
    ! [A_39] : k5_xboole_0(k1_xboole_0,A_39) = k2_xboole_0(k1_xboole_0,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_20])).

tff(c_605,plain,(
    ! [A_39] : k5_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_316])).

tff(c_402,plain,(
    ! [A_17,C_43] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_43)) = k5_xboole_0(k1_xboole_0,C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_350])).

tff(c_828,plain,(
    ! [A_56,C_57] : k5_xboole_0(A_56,k5_xboole_0(A_56,C_57)) = C_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_402])).

tff(c_865,plain,(
    ! [B_42,A_41] : k5_xboole_0(B_42,k5_xboole_0(A_41,B_42)) = k5_xboole_0(A_41,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_828])).

tff(c_915,plain,(
    ! [B_58,A_59] : k5_xboole_0(B_58,k5_xboole_0(A_59,B_58)) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_865])).

tff(c_827,plain,(
    ! [A_17,C_43] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_43)) = C_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_402])).

tff(c_924,plain,(
    ! [B_58,A_59] : k5_xboole_0(B_58,A_59) = k5_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_827])).

tff(c_274,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_268])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_265,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_244])).

tff(c_273,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_265])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_259,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_244])).

tff(c_3054,plain,(
    ! [A_102,B_103,C_104] : k5_xboole_0(A_102,k5_xboole_0(k3_xboole_0(A_102,B_103),C_104)) = k5_xboole_0(k4_xboole_0(A_102,B_103),C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_350])).

tff(c_3110,plain,(
    ! [A_102,B_103,B_4] : k5_xboole_0(k4_xboole_0(A_102,B_103),k3_xboole_0(B_4,k3_xboole_0(A_102,B_103))) = k5_xboole_0(A_102,k4_xboole_0(k3_xboole_0(A_102,B_103),B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_3054])).

tff(c_3174,plain,(
    ! [A_102,B_103,B_4] : k5_xboole_0(k4_xboole_0(A_102,B_103),k3_xboole_0(B_4,k3_xboole_0(A_102,B_103))) = k4_xboole_0(A_102,k4_xboole_0(B_103,B_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_3110])).

tff(c_6529,plain,(
    ! [A_156,B_157,B_158] : k5_xboole_0(A_156,k5_xboole_0(B_157,k3_xboole_0(k5_xboole_0(A_156,B_157),B_158))) = k4_xboole_0(k5_xboole_0(A_156,B_157),B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_350])).

tff(c_6704,plain,(
    ! [A_18,B_19,B_158] : k5_xboole_0(A_18,k5_xboole_0(k4_xboole_0(B_19,A_18),k3_xboole_0(k2_xboole_0(A_18,B_19),B_158))) = k4_xboole_0(k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)),B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6529])).

tff(c_59687,plain,(
    ! [A_500,B_501,B_502] : k5_xboole_0(A_500,k5_xboole_0(k4_xboole_0(B_501,A_500),k3_xboole_0(k2_xboole_0(A_500,B_501),B_502))) = k4_xboole_0(k2_xboole_0(A_500,B_501),B_502) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6704])).

tff(c_59855,plain,(
    ! [B_103,A_102] : k5_xboole_0(B_103,k4_xboole_0(A_102,k4_xboole_0(B_103,k2_xboole_0(B_103,A_102)))) = k4_xboole_0(k2_xboole_0(B_103,A_102),k3_xboole_0(A_102,B_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3174,c_59687])).

tff(c_110843,plain,(
    ! [B_697,A_698] : k4_xboole_0(k2_xboole_0(B_697,A_698),k3_xboole_0(A_698,B_697)) = k5_xboole_0(B_697,A_698) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_273,c_59855])).

tff(c_111482,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_110843])).

tff(c_22,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k5_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_193903,plain,(
    k5_xboole_0('#skF_2','#skF_1') != k5_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111482,c_22])).

tff(c_193906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_924,c_193903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 58.25/49.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.25/49.28  
% 58.25/49.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.25/49.28  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 58.25/49.28  
% 58.25/49.28  %Foreground sorts:
% 58.25/49.28  
% 58.25/49.28  
% 58.25/49.28  %Background operators:
% 58.25/49.28  
% 58.25/49.28  
% 58.25/49.28  %Foreground operators:
% 58.25/49.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 58.25/49.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 58.25/49.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 58.25/49.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 58.25/49.28  tff('#skF_2', type, '#skF_2': $i).
% 58.25/49.28  tff('#skF_1', type, '#skF_1': $i).
% 58.25/49.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 58.25/49.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 58.25/49.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 58.25/49.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 58.25/49.28  
% 58.25/49.29  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 58.25/49.29  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 58.25/49.29  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 58.25/49.29  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 58.25/49.29  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 58.25/49.29  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 58.25/49.29  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 58.25/49.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 58.25/49.29  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 58.25/49.29  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 58.25/49.29  tff(f_48, negated_conjecture, ~(![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 58.25/49.29  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_39])).
% 58.25/49.29  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 58.25/49.29  tff(c_350, plain, (![A_41, B_42, C_43]: (k5_xboole_0(k5_xboole_0(A_41, B_42), C_43)=k5_xboole_0(A_41, k5_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 58.25/49.29  tff(c_406, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k5_xboole_0(B_42, k5_xboole_0(A_41, B_42)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_350])).
% 58.25/49.29  tff(c_104, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 58.25/49.29  tff(c_10, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 58.25/49.29  tff(c_120, plain, (![A_28]: (k3_xboole_0(k1_xboole_0, A_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_10])).
% 58.25/49.29  tff(c_275, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k3_xboole_0(A_36, B_37), C_38)=k3_xboole_0(A_36, k4_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 58.25/49.29  tff(c_290, plain, (![A_28, C_38]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(A_28, C_38))=k4_xboole_0(k1_xboole_0, C_38))), inference(superposition, [status(thm), theory('equality')], [c_120, c_275])).
% 58.25/49.29  tff(c_328, plain, (![C_40]: (k4_xboole_0(k1_xboole_0, C_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_290])).
% 58.25/49.29  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 58.25/49.29  tff(c_337, plain, (![C_40]: (k5_xboole_0(C_40, k1_xboole_0)=k2_xboole_0(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_328, c_20])).
% 58.25/49.29  tff(c_413, plain, (![C_44]: (k2_xboole_0(C_44, k1_xboole_0)=C_44)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_337])).
% 58.25/49.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 58.25/49.29  tff(c_425, plain, (![C_44]: (k2_xboole_0(k1_xboole_0, C_44)=C_44)), inference(superposition, [status(thm), theory('equality')], [c_413, c_2])).
% 58.25/49.29  tff(c_244, plain, (![A_34, B_35]: (k5_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 58.25/49.29  tff(c_268, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_244])).
% 58.25/49.29  tff(c_306, plain, (![A_39]: (k4_xboole_0(A_39, k1_xboole_0)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_268])).
% 58.25/49.29  tff(c_316, plain, (![A_39]: (k5_xboole_0(k1_xboole_0, A_39)=k2_xboole_0(k1_xboole_0, A_39))), inference(superposition, [status(thm), theory('equality')], [c_306, c_20])).
% 58.25/49.29  tff(c_605, plain, (![A_39]: (k5_xboole_0(k1_xboole_0, A_39)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_425, c_316])).
% 58.25/49.29  tff(c_402, plain, (![A_17, C_43]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_43))=k5_xboole_0(k1_xboole_0, C_43))), inference(superposition, [status(thm), theory('equality')], [c_18, c_350])).
% 58.25/49.29  tff(c_828, plain, (![A_56, C_57]: (k5_xboole_0(A_56, k5_xboole_0(A_56, C_57))=C_57)), inference(demodulation, [status(thm), theory('equality')], [c_605, c_402])).
% 58.25/49.29  tff(c_865, plain, (![B_42, A_41]: (k5_xboole_0(B_42, k5_xboole_0(A_41, B_42))=k5_xboole_0(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_406, c_828])).
% 58.25/49.29  tff(c_915, plain, (![B_58, A_59]: (k5_xboole_0(B_58, k5_xboole_0(A_59, B_58))=A_59)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_865])).
% 58.25/49.29  tff(c_827, plain, (![A_17, C_43]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_43))=C_43)), inference(demodulation, [status(thm), theory('equality')], [c_605, c_402])).
% 58.25/49.29  tff(c_924, plain, (![B_58, A_59]: (k5_xboole_0(B_58, A_59)=k5_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_915, c_827])).
% 58.25/49.29  tff(c_274, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_268])).
% 58.25/49.29  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.25/49.29  tff(c_265, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_244])).
% 58.25/49.29  tff(c_273, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_265])).
% 58.25/49.29  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 58.25/49.29  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 58.25/49.29  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 58.25/49.29  tff(c_259, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_244])).
% 58.25/49.29  tff(c_3054, plain, (![A_102, B_103, C_104]: (k5_xboole_0(A_102, k5_xboole_0(k3_xboole_0(A_102, B_103), C_104))=k5_xboole_0(k4_xboole_0(A_102, B_103), C_104))), inference(superposition, [status(thm), theory('equality')], [c_6, c_350])).
% 58.25/49.29  tff(c_3110, plain, (![A_102, B_103, B_4]: (k5_xboole_0(k4_xboole_0(A_102, B_103), k3_xboole_0(B_4, k3_xboole_0(A_102, B_103)))=k5_xboole_0(A_102, k4_xboole_0(k3_xboole_0(A_102, B_103), B_4)))), inference(superposition, [status(thm), theory('equality')], [c_259, c_3054])).
% 58.25/49.29  tff(c_3174, plain, (![A_102, B_103, B_4]: (k5_xboole_0(k4_xboole_0(A_102, B_103), k3_xboole_0(B_4, k3_xboole_0(A_102, B_103)))=k4_xboole_0(A_102, k4_xboole_0(B_103, B_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_3110])).
% 58.25/49.29  tff(c_6529, plain, (![A_156, B_157, B_158]: (k5_xboole_0(A_156, k5_xboole_0(B_157, k3_xboole_0(k5_xboole_0(A_156, B_157), B_158)))=k4_xboole_0(k5_xboole_0(A_156, B_157), B_158))), inference(superposition, [status(thm), theory('equality')], [c_6, c_350])).
% 58.25/49.29  tff(c_6704, plain, (![A_18, B_19, B_158]: (k5_xboole_0(A_18, k5_xboole_0(k4_xboole_0(B_19, A_18), k3_xboole_0(k2_xboole_0(A_18, B_19), B_158)))=k4_xboole_0(k5_xboole_0(A_18, k4_xboole_0(B_19, A_18)), B_158))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6529])).
% 58.25/49.29  tff(c_59687, plain, (![A_500, B_501, B_502]: (k5_xboole_0(A_500, k5_xboole_0(k4_xboole_0(B_501, A_500), k3_xboole_0(k2_xboole_0(A_500, B_501), B_502)))=k4_xboole_0(k2_xboole_0(A_500, B_501), B_502))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6704])).
% 58.25/49.29  tff(c_59855, plain, (![B_103, A_102]: (k5_xboole_0(B_103, k4_xboole_0(A_102, k4_xboole_0(B_103, k2_xboole_0(B_103, A_102))))=k4_xboole_0(k2_xboole_0(B_103, A_102), k3_xboole_0(A_102, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_3174, c_59687])).
% 58.25/49.29  tff(c_110843, plain, (![B_697, A_698]: (k4_xboole_0(k2_xboole_0(B_697, A_698), k3_xboole_0(A_698, B_697))=k5_xboole_0(B_697, A_698))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_273, c_59855])).
% 58.25/49.29  tff(c_111482, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k5_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_110843])).
% 58.25/49.29  tff(c_22, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k5_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 58.25/49.29  tff(c_193903, plain, (k5_xboole_0('#skF_2', '#skF_1')!=k5_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111482, c_22])).
% 58.25/49.29  tff(c_193906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_924, c_193903])).
% 58.25/49.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.25/49.29  
% 58.25/49.29  Inference rules
% 58.25/49.29  ----------------------
% 58.25/49.29  #Ref     : 0
% 58.25/49.29  #Sup     : 48626
% 58.25/49.29  #Fact    : 0
% 58.25/49.29  #Define  : 0
% 58.25/49.29  #Split   : 0
% 58.25/49.29  #Chain   : 0
% 58.25/49.29  #Close   : 0
% 58.25/49.29  
% 58.25/49.29  Ordering : KBO
% 58.25/49.29  
% 58.25/49.29  Simplification rules
% 58.25/49.29  ----------------------
% 58.25/49.29  #Subsume      : 770
% 58.25/49.29  #Demod        : 76626
% 58.25/49.29  #Tautology    : 26070
% 58.25/49.29  #SimpNegUnit  : 0
% 58.25/49.29  #BackRed      : 21
% 58.25/49.29  
% 58.25/49.29  #Partial instantiations: 0
% 58.25/49.29  #Strategies tried      : 1
% 58.25/49.29  
% 58.25/49.29  Timing (in seconds)
% 58.25/49.29  ----------------------
% 58.25/49.30  Preprocessing        : 0.31
% 58.25/49.30  Parsing              : 0.16
% 58.25/49.30  CNF conversion       : 0.02
% 58.37/49.30  Main loop            : 48.14
% 58.37/49.30  Inferencing          : 4.16
% 58.37/49.30  Reduction            : 35.47
% 58.37/49.30  Demodulation         : 34.03
% 58.37/49.30  BG Simplification    : 0.69
% 58.37/49.30  Subsumption          : 6.61
% 58.37/49.30  Abstraction          : 1.49
% 58.37/49.30  MUC search           : 0.00
% 58.37/49.30  Cooper               : 0.00
% 58.37/49.30  Total                : 48.49
% 58.37/49.30  Index Insertion      : 0.00
% 58.37/49.30  Index Deletion       : 0.00
% 58.37/49.30  Index Matching       : 0.00
% 58.37/49.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
