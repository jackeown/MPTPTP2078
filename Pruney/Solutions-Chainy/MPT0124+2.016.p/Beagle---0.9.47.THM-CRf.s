%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:37 EST 2020

% Result     : Theorem 7.40s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 160 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 169 expanded)
%              Number of equality atoms :   47 ( 122 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(C,B)
       => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_82,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [A_32,B_33] : r1_tarski(k3_xboole_0(A_32,B_33),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),A_32) = A_32 ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,k4_xboole_0(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_1460,plain,(
    ! [A_30,B_31] : k3_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_85])).

tff(c_260,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k3_xboole_0(A_46,B_47),C_48) = k3_xboole_0(A_46,k4_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4866,plain,(
    ! [C_190,A_191,B_192] : k5_xboole_0(C_190,k3_xboole_0(A_191,k4_xboole_0(B_192,C_190))) = k2_xboole_0(C_190,k3_xboole_0(A_191,B_192)) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_18])).

tff(c_4884,plain,(
    ! [B_31,A_30] : k5_xboole_0(B_31,k4_xboole_0(A_30,B_31)) = k2_xboole_0(B_31,k3_xboole_0(A_30,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1460,c_4866])).

tff(c_4999,plain,(
    ! [B_197,A_198] : k2_xboole_0(B_197,k3_xboole_0(A_198,A_198)) = k2_xboole_0(B_197,A_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4884])).

tff(c_60,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_5097,plain,(
    ! [A_198,B_6] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_198,A_198),B_6),A_198) = k3_xboole_0(A_198,A_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_4999,c_67])).

tff(c_5190,plain,(
    ! [A_199] : k3_xboole_0(A_199,A_199) = A_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_14,c_5097])).

tff(c_5472,plain,(
    ! [A_199] : k2_xboole_0(A_199,A_199) = A_199 ),
    inference(superposition,[status(thm),theory(equality)],[c_5190,c_113])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_452,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k4_xboole_0(A_57,B_58),C_59) = k4_xboole_0(A_57,k2_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_504,plain,(
    ! [A_10,B_11,C_59] : k4_xboole_0(A_10,k2_xboole_0(k3_xboole_0(A_10,B_11),C_59)) = k4_xboole_0(k4_xboole_0(A_10,B_11),C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_452])).

tff(c_3379,plain,(
    ! [A_171,B_172,C_173] : k4_xboole_0(A_171,k2_xboole_0(k3_xboole_0(A_171,B_172),C_173)) = k4_xboole_0(A_171,k2_xboole_0(B_172,C_173)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_504])).

tff(c_3572,plain,(
    ! [A_174,B_175] : k4_xboole_0(A_174,k2_xboole_0(B_175,A_174)) = k4_xboole_0(A_174,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_3379])).

tff(c_468,plain,(
    ! [C_59,A_57,B_58] : k5_xboole_0(C_59,k4_xboole_0(A_57,k2_xboole_0(B_58,C_59))) = k2_xboole_0(C_59,k4_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_18])).

tff(c_3582,plain,(
    ! [A_174,B_175] : k5_xboole_0(A_174,k4_xboole_0(A_174,A_174)) = k2_xboole_0(A_174,k4_xboole_0(A_174,B_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3572,c_468])).

tff(c_3987,plain,(
    ! [A_178,B_179] : k2_xboole_0(A_178,k4_xboole_0(A_178,B_179)) = k2_xboole_0(A_178,A_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3582])).

tff(c_4053,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3987])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_720,plain,(
    ! [A_67,B_68,C_69] : r1_tarski(k4_xboole_0(A_67,k2_xboole_0(B_68,C_69)),k4_xboole_0(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_6])).

tff(c_963,plain,(
    ! [A_79,A_80,B_81] : r1_tarski(k4_xboole_0(A_79,A_80),k4_xboole_0(A_79,k4_xboole_0(A_80,B_81))) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_720])).

tff(c_1001,plain,(
    ! [A_12,B_13,B_81] : r1_tarski(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,k4_xboole_0(k4_xboole_0(A_12,B_13),B_81))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_963])).

tff(c_2084,plain,(
    ! [A_126,B_127,B_128] : r1_tarski(k3_xboole_0(A_126,B_127),k3_xboole_0(A_126,k2_xboole_0(B_127,B_128))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_1001])).

tff(c_2137,plain,(
    ! [A_129] : r1_tarski(k3_xboole_0(A_129,'#skF_3'),k3_xboole_0(A_129,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2084])).

tff(c_2157,plain,(
    ! [A_129] : k2_xboole_0(k3_xboole_0(A_129,'#skF_3'),k3_xboole_0(A_129,'#skF_2')) = k3_xboole_0(A_129,'#skF_2') ),
    inference(resolution,[status(thm)],[c_2137,c_4])).

tff(c_5298,plain,(
    k2_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5190,c_2157])).

tff(c_5515,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4053,c_5298])).

tff(c_8081,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5472,c_5515])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k4_xboole_0(A_17,B_18),k3_xboole_0(A_17,C_19)) = k4_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_24,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_23])).

tff(c_25,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_8086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8081,c_25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:44:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.40/2.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.40/2.86  
% 7.40/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.40/2.86  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 7.40/2.86  
% 7.40/2.86  %Foreground sorts:
% 7.40/2.86  
% 7.40/2.86  
% 7.40/2.86  %Background operators:
% 7.40/2.86  
% 7.40/2.86  
% 7.40/2.86  %Foreground operators:
% 7.40/2.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.40/2.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.40/2.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.40/2.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.40/2.86  tff('#skF_2', type, '#skF_2': $i).
% 7.40/2.86  tff('#skF_3', type, '#skF_3': $i).
% 7.40/2.86  tff('#skF_1', type, '#skF_1': $i).
% 7.40/2.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.40/2.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.40/2.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.40/2.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.40/2.86  
% 7.40/2.88  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.40/2.88  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.40/2.88  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.40/2.88  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.40/2.88  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.40/2.88  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.40/2.88  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.40/2.88  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 7.40/2.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.40/2.88  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 7.40/2.88  tff(c_82, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.40/2.88  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.40/2.88  tff(c_103, plain, (![A_32, B_33]: (r1_tarski(k3_xboole_0(A_32, B_33), A_32))), inference(superposition, [status(thm), theory('equality')], [c_82, c_6])).
% 7.40/2.88  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.40/2.88  tff(c_113, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), A_32)=A_32)), inference(resolution, [status(thm)], [c_103, c_4])).
% 7.40/2.88  tff(c_14, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.40/2.88  tff(c_18, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.40/2.88  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.40/2.88  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.40/2.88  tff(c_85, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k3_xboole_0(A_30, k4_xboole_0(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 7.40/2.88  tff(c_1460, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_85])).
% 7.40/2.88  tff(c_260, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k3_xboole_0(A_46, B_47), C_48)=k3_xboole_0(A_46, k4_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.40/2.88  tff(c_4866, plain, (![C_190, A_191, B_192]: (k5_xboole_0(C_190, k3_xboole_0(A_191, k4_xboole_0(B_192, C_190)))=k2_xboole_0(C_190, k3_xboole_0(A_191, B_192)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_18])).
% 7.40/2.88  tff(c_4884, plain, (![B_31, A_30]: (k5_xboole_0(B_31, k4_xboole_0(A_30, B_31))=k2_xboole_0(B_31, k3_xboole_0(A_30, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_1460, c_4866])).
% 7.40/2.88  tff(c_4999, plain, (![B_197, A_198]: (k2_xboole_0(B_197, k3_xboole_0(A_198, A_198))=k2_xboole_0(B_197, A_198))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4884])).
% 7.40/2.88  tff(c_60, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.40/2.88  tff(c_67, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_60])).
% 7.40/2.88  tff(c_5097, plain, (![A_198, B_6]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_198, A_198), B_6), A_198)=k3_xboole_0(A_198, A_198))), inference(superposition, [status(thm), theory('equality')], [c_4999, c_67])).
% 7.40/2.88  tff(c_5190, plain, (![A_199]: (k3_xboole_0(A_199, A_199)=A_199)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_14, c_5097])).
% 7.40/2.88  tff(c_5472, plain, (![A_199]: (k2_xboole_0(A_199, A_199)=A_199)), inference(superposition, [status(thm), theory('equality')], [c_5190, c_113])).
% 7.40/2.88  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.40/2.88  tff(c_452, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k4_xboole_0(A_57, B_58), C_59)=k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.40/2.88  tff(c_504, plain, (![A_10, B_11, C_59]: (k4_xboole_0(A_10, k2_xboole_0(k3_xboole_0(A_10, B_11), C_59))=k4_xboole_0(k4_xboole_0(A_10, B_11), C_59))), inference(superposition, [status(thm), theory('equality')], [c_10, c_452])).
% 7.40/2.88  tff(c_3379, plain, (![A_171, B_172, C_173]: (k4_xboole_0(A_171, k2_xboole_0(k3_xboole_0(A_171, B_172), C_173))=k4_xboole_0(A_171, k2_xboole_0(B_172, C_173)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_504])).
% 7.40/2.88  tff(c_3572, plain, (![A_174, B_175]: (k4_xboole_0(A_174, k2_xboole_0(B_175, A_174))=k4_xboole_0(A_174, A_174))), inference(superposition, [status(thm), theory('equality')], [c_113, c_3379])).
% 7.40/2.88  tff(c_468, plain, (![C_59, A_57, B_58]: (k5_xboole_0(C_59, k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)))=k2_xboole_0(C_59, k4_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_452, c_18])).
% 7.40/2.88  tff(c_3582, plain, (![A_174, B_175]: (k5_xboole_0(A_174, k4_xboole_0(A_174, A_174))=k2_xboole_0(A_174, k4_xboole_0(A_174, B_175)))), inference(superposition, [status(thm), theory('equality')], [c_3572, c_468])).
% 7.40/2.88  tff(c_3987, plain, (![A_178, B_179]: (k2_xboole_0(A_178, k4_xboole_0(A_178, B_179))=k2_xboole_0(A_178, A_178))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3582])).
% 7.40/2.88  tff(c_4053, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3987])).
% 7.40/2.88  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.40/2.88  tff(c_68, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_60])).
% 7.40/2.88  tff(c_720, plain, (![A_67, B_68, C_69]: (r1_tarski(k4_xboole_0(A_67, k2_xboole_0(B_68, C_69)), k4_xboole_0(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_452, c_6])).
% 7.40/2.88  tff(c_963, plain, (![A_79, A_80, B_81]: (r1_tarski(k4_xboole_0(A_79, A_80), k4_xboole_0(A_79, k4_xboole_0(A_80, B_81))))), inference(superposition, [status(thm), theory('equality')], [c_67, c_720])).
% 7.40/2.88  tff(c_1001, plain, (![A_12, B_13, B_81]: (r1_tarski(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, k4_xboole_0(k4_xboole_0(A_12, B_13), B_81))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_963])).
% 7.40/2.88  tff(c_2084, plain, (![A_126, B_127, B_128]: (r1_tarski(k3_xboole_0(A_126, B_127), k3_xboole_0(A_126, k2_xboole_0(B_127, B_128))))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_1001])).
% 7.40/2.88  tff(c_2137, plain, (![A_129]: (r1_tarski(k3_xboole_0(A_129, '#skF_3'), k3_xboole_0(A_129, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2084])).
% 7.40/2.88  tff(c_2157, plain, (![A_129]: (k2_xboole_0(k3_xboole_0(A_129, '#skF_3'), k3_xboole_0(A_129, '#skF_2'))=k3_xboole_0(A_129, '#skF_2'))), inference(resolution, [status(thm)], [c_2137, c_4])).
% 7.40/2.88  tff(c_5298, plain, (k2_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5190, c_2157])).
% 7.40/2.88  tff(c_5515, plain, (k3_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4053, c_5298])).
% 7.40/2.88  tff(c_8081, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5472, c_5515])).
% 7.40/2.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.40/2.88  tff(c_16, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k4_xboole_0(A_17, B_18), k3_xboole_0(A_17, C_19))=k4_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.40/2.88  tff(c_20, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.40/2.88  tff(c_23, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 7.40/2.88  tff(c_24, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_23])).
% 7.40/2.88  tff(c_25, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 7.40/2.88  tff(c_8086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8081, c_25])).
% 7.40/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.40/2.88  
% 7.40/2.88  Inference rules
% 7.40/2.88  ----------------------
% 7.40/2.88  #Ref     : 0
% 7.40/2.88  #Sup     : 1997
% 7.40/2.88  #Fact    : 0
% 7.40/2.88  #Define  : 0
% 7.40/2.88  #Split   : 0
% 7.40/2.88  #Chain   : 0
% 7.40/2.88  #Close   : 0
% 7.40/2.88  
% 7.40/2.88  Ordering : KBO
% 7.40/2.88  
% 7.40/2.88  Simplification rules
% 7.40/2.88  ----------------------
% 7.40/2.88  #Subsume      : 20
% 7.40/2.88  #Demod        : 1682
% 7.40/2.88  #Tautology    : 905
% 7.40/2.88  #SimpNegUnit  : 0
% 7.40/2.88  #BackRed      : 14
% 7.40/2.88  
% 7.40/2.88  #Partial instantiations: 0
% 7.40/2.88  #Strategies tried      : 1
% 7.40/2.88  
% 7.40/2.88  Timing (in seconds)
% 7.40/2.88  ----------------------
% 7.40/2.88  Preprocessing        : 0.41
% 7.40/2.88  Parsing              : 0.24
% 7.40/2.88  CNF conversion       : 0.02
% 7.40/2.88  Main loop            : 1.64
% 7.40/2.88  Inferencing          : 0.40
% 7.40/2.88  Reduction            : 0.85
% 7.40/2.88  Demodulation         : 0.73
% 7.40/2.88  BG Simplification    : 0.06
% 7.40/2.88  Subsumption          : 0.24
% 7.40/2.88  Abstraction          : 0.09
% 7.40/2.89  MUC search           : 0.00
% 7.40/2.89  Cooper               : 0.00
% 7.40/2.89  Total                : 2.09
% 7.40/2.89  Index Insertion      : 0.00
% 7.40/2.89  Index Deletion       : 0.00
% 7.40/2.89  Index Matching       : 0.00
% 7.40/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
