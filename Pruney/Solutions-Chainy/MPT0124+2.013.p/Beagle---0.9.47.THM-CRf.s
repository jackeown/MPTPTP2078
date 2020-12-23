%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:36 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 152 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :   56 ( 158 expanded)
%              Number of equality atoms :   45 ( 126 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(C,B)
       => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_82,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_176,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_188,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_176])).

tff(c_216,plain,(
    ! [A_49,B_50] : k3_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_188])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_231,plain,(
    ! [A_49,B_50] : k2_xboole_0(k4_xboole_0(A_49,B_50),A_49) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_93])).

tff(c_237,plain,(
    ! [A_49,B_50] : r1_tarski(k4_xboole_0(A_49,B_50),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_8])).

tff(c_283,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(A_55,k4_xboole_0(B_56,A_55)) = B_56
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_292,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(k4_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = A_17
      | ~ r1_tarski(k4_xboole_0(A_17,B_18),A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_283])).

tff(c_1054,plain,(
    ! [A_87,B_88] : k2_xboole_0(k4_xboole_0(A_87,B_88),k3_xboole_0(A_87,B_88)) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_292])).

tff(c_22,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k4_xboole_0(A_24,B_25),k3_xboole_0(A_24,C_26)) = k4_xboole_0(A_24,k4_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1106,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(B_90,B_90)) = A_89 ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_22])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(A_3,C_5)) = k4_xboole_0(A_3,k3_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1125,plain,(
    ! [A_89,B_4,B_90] : k4_xboole_0(A_89,k3_xboole_0(B_4,k4_xboole_0(B_90,B_90))) = k2_xboole_0(k4_xboole_0(A_89,B_4),A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_4])).

tff(c_3070,plain,(
    ! [A_128,B_129,B_130] : k4_xboole_0(A_128,k3_xboole_0(B_129,k4_xboole_0(B_130,B_130))) = A_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_1125])).

tff(c_3292,plain,(
    ! [A_128,B_130,B_2] : k4_xboole_0(A_128,k3_xboole_0(k4_xboole_0(B_130,B_130),B_2)) = A_128 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3070])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k3_xboole_0(A_19,B_20),C_21) = k3_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3855,plain,(
    ! [A_140,B_141,B_142] : k4_xboole_0(A_140,k3_xboole_0(k4_xboole_0(B_141,B_141),B_142)) = A_140 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3070])).

tff(c_3971,plain,(
    ! [A_140,B_141,B_142,C_26] : k4_xboole_0(A_140,k4_xboole_0(k3_xboole_0(k4_xboole_0(B_141,B_141),B_142),C_26)) = k2_xboole_0(A_140,k3_xboole_0(A_140,C_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3855,c_22])).

tff(c_4120,plain,(
    ! [A_140,C_26] : k2_xboole_0(A_140,k3_xboole_0(A_140,C_26)) = A_140 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3292,c_18,c_3971])).

tff(c_1203,plain,(
    ! [B_18] : k3_xboole_0(B_18,B_18) = B_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1106])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_749,plain,(
    ! [A_75,B_76,C_77] : k2_xboole_0(k4_xboole_0(A_75,B_76),k3_xboole_0(A_75,C_77)) = k4_xboole_0(A_75,k4_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_773,plain,(
    ! [A_17,B_18,C_77] : k4_xboole_0(A_17,k4_xboole_0(k4_xboole_0(A_17,B_18),C_77)) = k2_xboole_0(k3_xboole_0(A_17,B_18),k3_xboole_0(A_17,C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_749])).

tff(c_4325,plain,(
    ! [A_149,B_150,C_151] : k2_xboole_0(k3_xboole_0(A_149,B_150),k3_xboole_0(A_149,C_151)) = k3_xboole_0(A_149,k2_xboole_0(B_150,C_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10,c_773])).

tff(c_4360,plain,(
    ! [B_18,C_151] : k3_xboole_0(B_18,k2_xboole_0(B_18,C_151)) = k2_xboole_0(B_18,k3_xboole_0(B_18,C_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_4325])).

tff(c_4656,plain,(
    ! [B_156,C_157] : k3_xboole_0(B_156,k2_xboole_0(B_156,C_157)) = B_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4120,c_4360])).

tff(c_4815,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4656])).

tff(c_26,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_29,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_30,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_29])).

tff(c_31,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_4843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.02  
% 5.17/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.02  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 5.17/2.02  
% 5.17/2.02  %Foreground sorts:
% 5.17/2.02  
% 5.17/2.02  
% 5.17/2.02  %Background operators:
% 5.17/2.02  
% 5.17/2.02  
% 5.17/2.02  %Foreground operators:
% 5.17/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.17/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.17/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.17/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.17/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.17/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.17/2.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.17/2.02  
% 5.17/2.03  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 5.17/2.03  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.17/2.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.17/2.03  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.17/2.03  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.17/2.03  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.17/2.03  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 5.17/2.03  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 5.17/2.03  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 5.17/2.03  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.17/2.03  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.17/2.03  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.17/2.03  tff(c_82, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.17/2.03  tff(c_94, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_28, c_82])).
% 5.17/2.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.17/2.03  tff(c_14, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.17/2.03  tff(c_16, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.17/2.03  tff(c_176, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.17/2.03  tff(c_188, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_176])).
% 5.17/2.03  tff(c_216, plain, (![A_49, B_50]: (k3_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_188])).
% 5.17/2.03  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.17/2.03  tff(c_93, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_82])).
% 5.17/2.03  tff(c_231, plain, (![A_49, B_50]: (k2_xboole_0(k4_xboole_0(A_49, B_50), A_49)=A_49)), inference(superposition, [status(thm), theory('equality')], [c_216, c_93])).
% 5.17/2.03  tff(c_237, plain, (![A_49, B_50]: (r1_tarski(k4_xboole_0(A_49, B_50), A_49))), inference(superposition, [status(thm), theory('equality')], [c_216, c_8])).
% 5.17/2.03  tff(c_283, plain, (![A_55, B_56]: (k2_xboole_0(A_55, k4_xboole_0(B_56, A_55))=B_56 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.17/2.03  tff(c_292, plain, (![A_17, B_18]: (k2_xboole_0(k4_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=A_17 | ~r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_16, c_283])).
% 5.17/2.03  tff(c_1054, plain, (![A_87, B_88]: (k2_xboole_0(k4_xboole_0(A_87, B_88), k3_xboole_0(A_87, B_88))=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_292])).
% 5.17/2.03  tff(c_22, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k4_xboole_0(A_24, B_25), k3_xboole_0(A_24, C_26))=k4_xboole_0(A_24, k4_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.17/2.03  tff(c_1106, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(B_90, B_90))=A_89)), inference(superposition, [status(thm), theory('equality')], [c_1054, c_22])).
% 5.17/2.03  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(A_3, C_5))=k4_xboole_0(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.17/2.03  tff(c_1125, plain, (![A_89, B_4, B_90]: (k4_xboole_0(A_89, k3_xboole_0(B_4, k4_xboole_0(B_90, B_90)))=k2_xboole_0(k4_xboole_0(A_89, B_4), A_89))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_4])).
% 5.17/2.03  tff(c_3070, plain, (![A_128, B_129, B_130]: (k4_xboole_0(A_128, k3_xboole_0(B_129, k4_xboole_0(B_130, B_130)))=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_231, c_1125])).
% 5.17/2.03  tff(c_3292, plain, (![A_128, B_130, B_2]: (k4_xboole_0(A_128, k3_xboole_0(k4_xboole_0(B_130, B_130), B_2))=A_128)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3070])).
% 5.17/2.03  tff(c_18, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k3_xboole_0(A_19, B_20), C_21)=k3_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.17/2.03  tff(c_3855, plain, (![A_140, B_141, B_142]: (k4_xboole_0(A_140, k3_xboole_0(k4_xboole_0(B_141, B_141), B_142))=A_140)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3070])).
% 5.17/2.03  tff(c_3971, plain, (![A_140, B_141, B_142, C_26]: (k4_xboole_0(A_140, k4_xboole_0(k3_xboole_0(k4_xboole_0(B_141, B_141), B_142), C_26))=k2_xboole_0(A_140, k3_xboole_0(A_140, C_26)))), inference(superposition, [status(thm), theory('equality')], [c_3855, c_22])).
% 5.17/2.03  tff(c_4120, plain, (![A_140, C_26]: (k2_xboole_0(A_140, k3_xboole_0(A_140, C_26))=A_140)), inference(demodulation, [status(thm), theory('equality')], [c_3292, c_18, c_3971])).
% 5.17/2.03  tff(c_1203, plain, (![B_18]: (k3_xboole_0(B_18, B_18)=B_18)), inference(superposition, [status(thm), theory('equality')], [c_16, c_1106])).
% 5.17/2.03  tff(c_10, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.17/2.03  tff(c_749, plain, (![A_75, B_76, C_77]: (k2_xboole_0(k4_xboole_0(A_75, B_76), k3_xboole_0(A_75, C_77))=k4_xboole_0(A_75, k4_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.17/2.03  tff(c_773, plain, (![A_17, B_18, C_77]: (k4_xboole_0(A_17, k4_xboole_0(k4_xboole_0(A_17, B_18), C_77))=k2_xboole_0(k3_xboole_0(A_17, B_18), k3_xboole_0(A_17, C_77)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_749])).
% 5.17/2.03  tff(c_4325, plain, (![A_149, B_150, C_151]: (k2_xboole_0(k3_xboole_0(A_149, B_150), k3_xboole_0(A_149, C_151))=k3_xboole_0(A_149, k2_xboole_0(B_150, C_151)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10, c_773])).
% 5.17/2.03  tff(c_4360, plain, (![B_18, C_151]: (k3_xboole_0(B_18, k2_xboole_0(B_18, C_151))=k2_xboole_0(B_18, k3_xboole_0(B_18, C_151)))), inference(superposition, [status(thm), theory('equality')], [c_1203, c_4325])).
% 5.17/2.03  tff(c_4656, plain, (![B_156, C_157]: (k3_xboole_0(B_156, k2_xboole_0(B_156, C_157))=B_156)), inference(demodulation, [status(thm), theory('equality')], [c_4120, c_4360])).
% 5.17/2.03  tff(c_4815, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_94, c_4656])).
% 5.17/2.03  tff(c_26, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.17/2.03  tff(c_29, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 5.17/2.03  tff(c_30, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_29])).
% 5.17/2.03  tff(c_31, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 5.17/2.03  tff(c_4843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4815, c_31])).
% 5.17/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.03  
% 5.17/2.03  Inference rules
% 5.17/2.03  ----------------------
% 5.17/2.03  #Ref     : 0
% 5.17/2.03  #Sup     : 1190
% 5.17/2.03  #Fact    : 0
% 5.17/2.03  #Define  : 0
% 5.17/2.03  #Split   : 0
% 5.17/2.03  #Chain   : 0
% 5.17/2.03  #Close   : 0
% 5.17/2.03  
% 5.17/2.03  Ordering : KBO
% 5.17/2.03  
% 5.17/2.03  Simplification rules
% 5.17/2.03  ----------------------
% 5.17/2.03  #Subsume      : 17
% 5.17/2.03  #Demod        : 874
% 5.17/2.03  #Tautology    : 553
% 5.17/2.03  #SimpNegUnit  : 0
% 5.17/2.03  #BackRed      : 1
% 5.17/2.03  
% 5.17/2.03  #Partial instantiations: 0
% 5.17/2.03  #Strategies tried      : 1
% 5.17/2.03  
% 5.17/2.03  Timing (in seconds)
% 5.17/2.03  ----------------------
% 5.17/2.04  Preprocessing        : 0.32
% 5.17/2.04  Parsing              : 0.17
% 5.17/2.04  CNF conversion       : 0.02
% 5.17/2.04  Main loop            : 0.92
% 5.17/2.04  Inferencing          : 0.27
% 5.17/2.04  Reduction            : 0.43
% 5.17/2.04  Demodulation         : 0.37
% 5.17/2.04  BG Simplification    : 0.04
% 5.17/2.04  Subsumption          : 0.13
% 5.17/2.04  Abstraction          : 0.06
% 5.17/2.04  MUC search           : 0.00
% 5.17/2.04  Cooper               : 0.00
% 5.17/2.04  Total                : 1.27
% 5.17/2.04  Index Insertion      : 0.00
% 5.17/2.04  Index Deletion       : 0.00
% 5.17/2.04  Index Matching       : 0.00
% 5.17/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
