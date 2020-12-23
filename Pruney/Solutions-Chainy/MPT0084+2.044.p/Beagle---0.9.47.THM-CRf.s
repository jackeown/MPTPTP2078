%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:10 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 136 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   65 ( 140 expanded)
%              Number of equality atoms :   53 ( 115 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_45,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_49,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_28])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_126,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_126])).

tff(c_163,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_150])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    ! [A_33,B_34] : k2_xboole_0(k3_xboole_0(A_33,B_34),k4_xboole_0(A_33,B_34)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_365,plain,(
    ! [A_42,B_43] : k4_xboole_0(k3_xboole_0(A_42,B_43),A_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_12])).

tff(c_1080,plain,(
    ! [C_61,B_62] : k3_xboole_0(C_61,k4_xboole_0(B_62,C_61)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_365])).

tff(c_14,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1104,plain,(
    ! [C_61,B_62] : k4_xboole_0(C_61,k4_xboole_0(B_62,C_61)) = k4_xboole_0(C_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_14])).

tff(c_1153,plain,(
    ! [C_61,B_62] : k4_xboole_0(C_61,k4_xboole_0(B_62,C_61)) = C_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1104])).

tff(c_153,plain,(
    ! [A_6,B_7] : k3_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_683,plain,(
    ! [A_51,B_52] : k3_xboole_0(A_51,k2_xboole_0(A_51,B_52)) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_153])).

tff(c_100,plain,(
    ! [A_33,B_34] : k4_xboole_0(k3_xboole_0(A_33,B_34),A_33) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_12])).

tff(c_696,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_100])).

tff(c_156,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_126])).

tff(c_740,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_156])).

tff(c_121,plain,(
    ! [A_5] : k2_xboole_0(k3_xboole_0(A_5,k1_xboole_0),A_5) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_94])).

tff(c_820,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_121])).

tff(c_497,plain,(
    ! [A_46,B_47,C_48] : k2_xboole_0(k4_xboole_0(A_46,B_47),k3_xboole_0(A_46,C_48)) = k4_xboole_0(A_46,k4_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_640,plain,(
    ! [C_50] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_50)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_497])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_649,plain,(
    ! [C_50] : k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_50))) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_16])).

tff(c_1575,plain,(
    ! [C_71] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_71)) = k4_xboole_0('#skF_1',C_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_820,c_649])).

tff(c_1607,plain,(
    ! [B_62] : k4_xboole_0('#skF_1',k4_xboole_0(B_62,'#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_1575])).

tff(c_1638,plain,(
    ! [B_62] : k4_xboole_0('#skF_1',k4_xboole_0(B_62,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1607])).

tff(c_20,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(A_15,B_16),k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_702,plain,(
    ! [A_51,B_52] : k2_xboole_0(A_51,k4_xboole_0(A_51,k2_xboole_0(A_51,B_52))) = A_51 ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_20])).

tff(c_733,plain,(
    ! [A_51] : k2_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_702])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_542,plain,(
    ! [B_47] : k4_xboole_0('#skF_1',k4_xboole_0(B_47,k3_xboole_0('#skF_2','#skF_3'))) = k2_xboole_0(k4_xboole_0('#skF_1',B_47),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_497])).

tff(c_1016,plain,(
    ! [B_60] : k4_xboole_0('#skF_1',k4_xboole_0(B_60,k3_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0('#skF_1',B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_542])).

tff(c_1065,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1016])).

tff(c_5283,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1638,c_1065])).

tff(c_1348,plain,(
    ! [C_66,B_67] : k4_xboole_0(C_66,k4_xboole_0(B_67,C_66)) = C_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1104])).

tff(c_395,plain,(
    ! [C_14,B_13] : k3_xboole_0(C_14,k4_xboole_0(B_13,C_14)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_365])).

tff(c_1368,plain,(
    ! [B_67,C_66] : k3_xboole_0(k4_xboole_0(B_67,C_66),C_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1348,c_395])).

tff(c_5316,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5283,c_1368])).

tff(c_5348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_5316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.84  
% 4.41/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.85  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.41/1.85  
% 4.41/1.85  %Foreground sorts:
% 4.41/1.85  
% 4.41/1.85  
% 4.41/1.85  %Background operators:
% 4.41/1.85  
% 4.41/1.85  
% 4.41/1.85  %Foreground operators:
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.41/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.41/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.41/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.41/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.41/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.41/1.85  
% 4.41/1.86  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.41/1.86  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.41/1.86  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.41/1.86  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.41/1.86  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.41/1.86  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.41/1.86  tff(f_45, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.41/1.86  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.41/1.86  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.41/1.86  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.41/1.86  tff(c_45, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.41/1.86  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.41/1.86  tff(c_49, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_45, c_28])).
% 4.41/1.86  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.41/1.86  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.41/1.86  tff(c_63, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.41/1.86  tff(c_67, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_63])).
% 4.41/1.86  tff(c_126, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.86  tff(c_150, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67, c_126])).
% 4.41/1.86  tff(c_163, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_150])).
% 4.41/1.86  tff(c_18, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.41/1.86  tff(c_94, plain, (![A_33, B_34]: (k2_xboole_0(k3_xboole_0(A_33, B_34), k4_xboole_0(A_33, B_34))=A_33)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.41/1.86  tff(c_12, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.41/1.86  tff(c_365, plain, (![A_42, B_43]: (k4_xboole_0(k3_xboole_0(A_42, B_43), A_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_12])).
% 4.41/1.86  tff(c_1080, plain, (![C_61, B_62]: (k3_xboole_0(C_61, k4_xboole_0(B_62, C_61))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_365])).
% 4.41/1.86  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.41/1.86  tff(c_1104, plain, (![C_61, B_62]: (k4_xboole_0(C_61, k4_xboole_0(B_62, C_61))=k4_xboole_0(C_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1080, c_14])).
% 4.41/1.86  tff(c_1153, plain, (![C_61, B_62]: (k4_xboole_0(C_61, k4_xboole_0(B_62, C_61))=C_61)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1104])).
% 4.41/1.86  tff(c_153, plain, (![A_6, B_7]: (k3_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k4_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_126])).
% 4.41/1.86  tff(c_683, plain, (![A_51, B_52]: (k3_xboole_0(A_51, k2_xboole_0(A_51, B_52))=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_153])).
% 4.41/1.86  tff(c_100, plain, (![A_33, B_34]: (k4_xboole_0(k3_xboole_0(A_33, B_34), A_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_12])).
% 4.41/1.86  tff(c_696, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_683, c_100])).
% 4.41/1.86  tff(c_156, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_126])).
% 4.41/1.86  tff(c_740, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_696, c_156])).
% 4.41/1.86  tff(c_121, plain, (![A_5]: (k2_xboole_0(k3_xboole_0(A_5, k1_xboole_0), A_5)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_10, c_94])).
% 4.41/1.86  tff(c_820, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_740, c_121])).
% 4.41/1.86  tff(c_497, plain, (![A_46, B_47, C_48]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k3_xboole_0(A_46, C_48))=k4_xboole_0(A_46, k4_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.41/1.86  tff(c_640, plain, (![C_50]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_50))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_50)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_497])).
% 4.41/1.86  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.86  tff(c_649, plain, (![C_50]: (k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_50)))=k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_50)))), inference(superposition, [status(thm), theory('equality')], [c_640, c_16])).
% 4.41/1.86  tff(c_1575, plain, (![C_71]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_71))=k4_xboole_0('#skF_1', C_71))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_820, c_649])).
% 4.41/1.86  tff(c_1607, plain, (![B_62]: (k4_xboole_0('#skF_1', k4_xboole_0(B_62, '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1153, c_1575])).
% 4.41/1.86  tff(c_1638, plain, (![B_62]: (k4_xboole_0('#skF_1', k4_xboole_0(B_62, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1607])).
% 4.41/1.86  tff(c_20, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(A_15, B_16), k4_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.41/1.86  tff(c_702, plain, (![A_51, B_52]: (k2_xboole_0(A_51, k4_xboole_0(A_51, k2_xboole_0(A_51, B_52)))=A_51)), inference(superposition, [status(thm), theory('equality')], [c_683, c_20])).
% 4.41/1.86  tff(c_733, plain, (![A_51]: (k2_xboole_0(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_702])).
% 4.41/1.86  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.41/1.86  tff(c_50, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.41/1.86  tff(c_58, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_50])).
% 4.41/1.86  tff(c_542, plain, (![B_47]: (k4_xboole_0('#skF_1', k4_xboole_0(B_47, k3_xboole_0('#skF_2', '#skF_3')))=k2_xboole_0(k4_xboole_0('#skF_1', B_47), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_497])).
% 4.41/1.86  tff(c_1016, plain, (![B_60]: (k4_xboole_0('#skF_1', k4_xboole_0(B_60, k3_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0('#skF_1', B_60))), inference(demodulation, [status(thm), theory('equality')], [c_733, c_542])).
% 4.41/1.86  tff(c_1065, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1016])).
% 4.41/1.86  tff(c_5283, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1638, c_1065])).
% 4.41/1.86  tff(c_1348, plain, (![C_66, B_67]: (k4_xboole_0(C_66, k4_xboole_0(B_67, C_66))=C_66)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1104])).
% 4.41/1.86  tff(c_395, plain, (![C_14, B_13]: (k3_xboole_0(C_14, k4_xboole_0(B_13, C_14))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_365])).
% 4.41/1.86  tff(c_1368, plain, (![B_67, C_66]: (k3_xboole_0(k4_xboole_0(B_67, C_66), C_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1348, c_395])).
% 4.41/1.86  tff(c_5316, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5283, c_1368])).
% 4.41/1.86  tff(c_5348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_5316])).
% 4.41/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.86  
% 4.41/1.86  Inference rules
% 4.41/1.86  ----------------------
% 4.41/1.86  #Ref     : 0
% 4.41/1.86  #Sup     : 1329
% 4.41/1.86  #Fact    : 0
% 4.41/1.86  #Define  : 0
% 4.41/1.86  #Split   : 0
% 4.41/1.86  #Chain   : 0
% 4.41/1.86  #Close   : 0
% 4.41/1.86  
% 4.41/1.86  Ordering : KBO
% 4.41/1.86  
% 4.41/1.86  Simplification rules
% 4.41/1.86  ----------------------
% 4.41/1.86  #Subsume      : 0
% 4.41/1.86  #Demod        : 1347
% 4.41/1.86  #Tautology    : 972
% 4.41/1.86  #SimpNegUnit  : 1
% 4.41/1.86  #BackRed      : 4
% 4.41/1.86  
% 4.41/1.86  #Partial instantiations: 0
% 4.41/1.86  #Strategies tried      : 1
% 4.41/1.86  
% 4.41/1.86  Timing (in seconds)
% 4.41/1.86  ----------------------
% 4.41/1.86  Preprocessing        : 0.30
% 4.41/1.86  Parsing              : 0.16
% 4.41/1.86  CNF conversion       : 0.02
% 4.41/1.86  Main loop            : 0.78
% 4.41/1.86  Inferencing          : 0.24
% 4.41/1.86  Reduction            : 0.37
% 4.41/1.86  Demodulation         : 0.30
% 4.41/1.86  BG Simplification    : 0.03
% 4.41/1.86  Subsumption          : 0.10
% 4.41/1.86  Abstraction          : 0.04
% 4.41/1.86  MUC search           : 0.00
% 4.41/1.86  Cooper               : 0.00
% 4.41/1.86  Total                : 1.11
% 4.41/1.86  Index Insertion      : 0.00
% 4.41/1.86  Index Deletion       : 0.00
% 4.41/1.86  Index Matching       : 0.00
% 4.41/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
