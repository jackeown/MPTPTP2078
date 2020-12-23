%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:41 EST 2020

% Result     : Theorem 23.50s
% Output     : CNFRefutation 23.63s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 109 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  99 expanded)
%              Number of equality atoms :   49 (  98 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_50,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_35] : k2_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_306,plain,(
    ! [A_47,B_48] : k2_xboole_0(A_47,k4_xboole_0(B_48,A_47)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_322,plain,(
    ! [B_48] : k4_xboole_0(B_48,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_66])).

tff(c_342,plain,(
    ! [B_48] : k4_xboole_0(B_48,k1_xboole_0) = B_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_322])).

tff(c_135,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(A_37,B_38)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_151,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_331,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_306])).

tff(c_345,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_331])).

tff(c_186,plain,(
    ! [A_41,B_42] : k3_xboole_0(A_41,k2_xboole_0(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_204,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_186])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_26,B_27] : k4_xboole_0(k2_xboole_0(A_26,B_27),k3_xboole_0(A_26,B_27)) = k2_xboole_0(k4_xboole_0(A_26,B_27),k4_xboole_0(B_27,A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_640,plain,(
    ! [A_59,B_60] : k4_xboole_0(k2_xboole_0(A_59,B_60),k3_xboole_0(A_59,B_60)) = k5_xboole_0(A_59,B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_670,plain,(
    ! [A_5] : k4_xboole_0(k2_xboole_0(A_5,A_5),A_5) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_640])).

tff(c_695,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_345,c_670])).

tff(c_33,plain,(
    ! [A_26,B_27] : k4_xboole_0(k2_xboole_0(A_26,B_27),k3_xboole_0(A_26,B_27)) = k5_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_993,plain,(
    ! [A_71,B_72] : k2_xboole_0(k5_xboole_0(A_71,B_72),k3_xboole_0(A_71,B_72)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1008,plain,(
    ! [A_71,B_72] : k4_xboole_0(k5_xboole_0(A_71,B_72),k3_xboole_0(A_71,B_72)) = k4_xboole_0(k2_xboole_0(A_71,B_72),k3_xboole_0(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_14])).

tff(c_7424,plain,(
    ! [A_163,B_164] : k4_xboole_0(k5_xboole_0(A_163,B_164),k3_xboole_0(A_163,B_164)) = k5_xboole_0(A_163,B_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_1008])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_148,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1697,plain,(
    ! [A_88,B_89] : k2_xboole_0(k4_xboole_0(A_88,B_89),k4_xboole_0(B_89,A_88)) = k5_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1818,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(k4_xboole_0(A_18,B_19),A_18)) = k5_xboole_0(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1697])).

tff(c_1880,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_148,c_16,c_1818])).

tff(c_7457,plain,(
    ! [A_163,B_164] : k5_xboole_0(k5_xboole_0(A_163,B_164),k5_xboole_0(A_163,B_164)) = k3_xboole_0(k5_xboole_0(A_163,B_164),k3_xboole_0(A_163,B_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7424,c_1880])).

tff(c_7576,plain,(
    ! [A_163,B_164] : k3_xboole_0(k5_xboole_0(A_163,B_164),k3_xboole_0(A_163,B_164)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_7457])).

tff(c_5910,plain,(
    ! [B_147,A_148] : k2_xboole_0(k4_xboole_0(B_147,A_148),k4_xboole_0(A_148,B_147)) = k5_xboole_0(A_148,B_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_2])).

tff(c_5956,plain,(
    ! [B_147,A_148] : k5_xboole_0(B_147,A_148) = k5_xboole_0(A_148,B_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_5910,c_4])).

tff(c_1005,plain,(
    ! [A_71,B_72] : k4_xboole_0(k2_xboole_0(A_71,B_72),k3_xboole_0(k5_xboole_0(A_71,B_72),k3_xboole_0(A_71,B_72))) = k5_xboole_0(k5_xboole_0(A_71,B_72),k3_xboole_0(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_33])).

tff(c_95045,plain,(
    ! [A_71,B_72] : k5_xboole_0(k3_xboole_0(A_71,B_72),k5_xboole_0(A_71,B_72)) = k2_xboole_0(A_71,B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_7576,c_5956,c_1005])).

tff(c_32,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6244,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5956,c_32])).

tff(c_95048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95045,c_6244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.50/16.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.50/16.48  
% 23.50/16.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.50/16.48  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 23.50/16.48  
% 23.50/16.48  %Foreground sorts:
% 23.50/16.48  
% 23.50/16.48  
% 23.50/16.48  %Background operators:
% 23.50/16.48  
% 23.50/16.48  
% 23.50/16.48  %Foreground operators:
% 23.50/16.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.50/16.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.50/16.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.50/16.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.50/16.48  tff('#skF_2', type, '#skF_2': $i).
% 23.50/16.48  tff('#skF_1', type, '#skF_1': $i).
% 23.50/16.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.50/16.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.50/16.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.50/16.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.50/16.48  
% 23.63/16.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 23.63/16.50  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 23.63/16.50  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 23.63/16.50  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 23.63/16.50  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 23.63/16.50  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 23.63/16.50  tff(f_51, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 23.63/16.50  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 23.63/16.50  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 23.63/16.50  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 23.63/16.50  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 23.63/16.50  tff(f_58, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 23.63/16.50  tff(c_50, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.63/16.50  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.63/16.50  tff(c_66, plain, (![A_35]: (k2_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_50, c_6])).
% 23.63/16.50  tff(c_306, plain, (![A_47, B_48]: (k2_xboole_0(A_47, k4_xboole_0(B_48, A_47))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.63/16.50  tff(c_322, plain, (![B_48]: (k4_xboole_0(B_48, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_48))), inference(superposition, [status(thm), theory('equality')], [c_306, c_66])).
% 23.63/16.50  tff(c_342, plain, (![B_48]: (k4_xboole_0(B_48, k1_xboole_0)=B_48)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_322])).
% 23.63/16.50  tff(c_135, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(A_37, B_38))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.63/16.50  tff(c_151, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_135])).
% 23.63/16.50  tff(c_331, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_151, c_306])).
% 23.63/16.50  tff(c_345, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_331])).
% 23.63/16.50  tff(c_186, plain, (![A_41, B_42]: (k3_xboole_0(A_41, k2_xboole_0(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.63/16.50  tff(c_204, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_6, c_186])).
% 23.63/16.50  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.63/16.50  tff(c_26, plain, (![A_26, B_27]: (k4_xboole_0(k2_xboole_0(A_26, B_27), k3_xboole_0(A_26, B_27))=k2_xboole_0(k4_xboole_0(A_26, B_27), k4_xboole_0(B_27, A_26)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 23.63/16.50  tff(c_640, plain, (![A_59, B_60]: (k4_xboole_0(k2_xboole_0(A_59, B_60), k3_xboole_0(A_59, B_60))=k5_xboole_0(A_59, B_60))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_26])).
% 23.63/16.50  tff(c_670, plain, (![A_5]: (k4_xboole_0(k2_xboole_0(A_5, A_5), A_5)=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_204, c_640])).
% 23.63/16.50  tff(c_695, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_151, c_345, c_670])).
% 23.63/16.50  tff(c_33, plain, (![A_26, B_27]: (k4_xboole_0(k2_xboole_0(A_26, B_27), k3_xboole_0(A_26, B_27))=k5_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_26])).
% 23.63/16.50  tff(c_993, plain, (![A_71, B_72]: (k2_xboole_0(k5_xboole_0(A_71, B_72), k3_xboole_0(A_71, B_72))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.63/16.50  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.63/16.50  tff(c_1008, plain, (![A_71, B_72]: (k4_xboole_0(k5_xboole_0(A_71, B_72), k3_xboole_0(A_71, B_72))=k4_xboole_0(k2_xboole_0(A_71, B_72), k3_xboole_0(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_993, c_14])).
% 23.63/16.50  tff(c_7424, plain, (![A_163, B_164]: (k4_xboole_0(k5_xboole_0(A_163, B_164), k3_xboole_0(A_163, B_164))=k5_xboole_0(A_163, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_1008])).
% 23.63/16.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.63/16.50  tff(c_148, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 23.63/16.50  tff(c_16, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.63/16.50  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.63/16.50  tff(c_1697, plain, (![A_88, B_89]: (k2_xboole_0(k4_xboole_0(A_88, B_89), k4_xboole_0(B_89, A_88))=k5_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.63/16.50  tff(c_1818, plain, (![A_18, B_19]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(k4_xboole_0(A_18, B_19), A_18))=k5_xboole_0(A_18, k4_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1697])).
% 23.63/16.50  tff(c_1880, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_148, c_16, c_1818])).
% 23.63/16.50  tff(c_7457, plain, (![A_163, B_164]: (k5_xboole_0(k5_xboole_0(A_163, B_164), k5_xboole_0(A_163, B_164))=k3_xboole_0(k5_xboole_0(A_163, B_164), k3_xboole_0(A_163, B_164)))), inference(superposition, [status(thm), theory('equality')], [c_7424, c_1880])).
% 23.63/16.50  tff(c_7576, plain, (![A_163, B_164]: (k3_xboole_0(k5_xboole_0(A_163, B_164), k3_xboole_0(A_163, B_164))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_695, c_7457])).
% 23.63/16.50  tff(c_5910, plain, (![B_147, A_148]: (k2_xboole_0(k4_xboole_0(B_147, A_148), k4_xboole_0(A_148, B_147))=k5_xboole_0(A_148, B_147))), inference(superposition, [status(thm), theory('equality')], [c_1697, c_2])).
% 23.63/16.50  tff(c_5956, plain, (![B_147, A_148]: (k5_xboole_0(B_147, A_148)=k5_xboole_0(A_148, B_147))), inference(superposition, [status(thm), theory('equality')], [c_5910, c_4])).
% 23.63/16.50  tff(c_1005, plain, (![A_71, B_72]: (k4_xboole_0(k2_xboole_0(A_71, B_72), k3_xboole_0(k5_xboole_0(A_71, B_72), k3_xboole_0(A_71, B_72)))=k5_xboole_0(k5_xboole_0(A_71, B_72), k3_xboole_0(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_993, c_33])).
% 23.63/16.50  tff(c_95045, plain, (![A_71, B_72]: (k5_xboole_0(k3_xboole_0(A_71, B_72), k5_xboole_0(A_71, B_72))=k2_xboole_0(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_7576, c_5956, c_1005])).
% 23.63/16.50  tff(c_32, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 23.63/16.50  tff(c_6244, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5956, c_32])).
% 23.63/16.50  tff(c_95048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95045, c_6244])).
% 23.63/16.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.63/16.50  
% 23.63/16.50  Inference rules
% 23.63/16.50  ----------------------
% 23.63/16.50  #Ref     : 0
% 23.63/16.50  #Sup     : 24146
% 23.63/16.50  #Fact    : 0
% 23.63/16.50  #Define  : 0
% 23.63/16.50  #Split   : 0
% 23.63/16.50  #Chain   : 0
% 23.63/16.50  #Close   : 0
% 23.63/16.50  
% 23.63/16.50  Ordering : KBO
% 23.63/16.50  
% 23.63/16.50  Simplification rules
% 23.63/16.50  ----------------------
% 23.63/16.50  #Subsume      : 181
% 23.63/16.50  #Demod        : 36095
% 23.63/16.50  #Tautology    : 13973
% 23.63/16.50  #SimpNegUnit  : 0
% 23.63/16.50  #BackRed      : 14
% 23.63/16.50  
% 23.63/16.50  #Partial instantiations: 0
% 23.63/16.50  #Strategies tried      : 1
% 23.63/16.50  
% 23.63/16.50  Timing (in seconds)
% 23.63/16.50  ----------------------
% 23.63/16.50  Preprocessing        : 0.30
% 23.63/16.50  Parsing              : 0.16
% 23.63/16.50  CNF conversion       : 0.02
% 23.63/16.50  Main loop            : 15.43
% 23.63/16.50  Inferencing          : 1.69
% 23.63/16.50  Reduction            : 10.68
% 23.63/16.50  Demodulation         : 10.06
% 23.63/16.50  BG Simplification    : 0.26
% 23.63/16.50  Subsumption          : 2.30
% 23.63/16.50  Abstraction          : 0.55
% 23.63/16.50  MUC search           : 0.00
% 23.63/16.50  Cooper               : 0.00
% 23.63/16.50  Total                : 15.76
% 23.63/16.50  Index Insertion      : 0.00
% 23.63/16.50  Index Deletion       : 0.00
% 23.63/16.50  Index Matching       : 0.00
% 23.63/16.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
