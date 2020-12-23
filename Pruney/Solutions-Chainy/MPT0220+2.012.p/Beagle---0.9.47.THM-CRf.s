%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:05 EST 2020

% Result     : Theorem 8.25s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 202 expanded)
%              Number of leaves         :   31 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :   59 ( 225 expanded)
%              Number of equality atoms :   49 ( 170 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_154,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k1_xboole_0
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_248,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_269,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_248])).

tff(c_275,plain,(
    ! [A_79] : k3_xboole_0(A_79,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_269])).

tff(c_16,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_280,plain,(
    ! [A_79] : k5_xboole_0(A_79,k1_xboole_0) = k4_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_16])).

tff(c_382,plain,(
    ! [A_83] : k5_xboole_0(A_83,k1_xboole_0) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_280])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_392,plain,(
    ! [A_83] : k5_xboole_0(k1_xboole_0,A_83) = A_83 ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_4])).

tff(c_42,plain,(
    ! [A_49,B_50] : r1_tarski(k1_tarski(A_49),k2_tarski(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_161,plain,(
    ! [A_49,B_50] : k4_xboole_0(k1_tarski(A_49),k2_tarski(A_49,B_50)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_154])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_209,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1115,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k3_xboole_0(B_128,A_127)) = k4_xboole_0(A_127,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_136,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_218,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_209])).

tff(c_227,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_218])).

tff(c_535,plain,(
    ! [A_89,B_90,C_91] : k5_xboole_0(k5_xboole_0(A_89,B_90),C_91) = k5_xboole_0(A_89,k5_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_589,plain,(
    ! [B_6,C_91] : k5_xboole_0(B_6,k5_xboole_0(B_6,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_535])).

tff(c_623,plain,(
    ! [B_6,C_91] : k5_xboole_0(B_6,k5_xboole_0(B_6,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_589])).

tff(c_1356,plain,(
    ! [A_137,B_138] : k5_xboole_0(A_137,k4_xboole_0(A_137,B_138)) = k3_xboole_0(B_138,A_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_623])).

tff(c_1416,plain,(
    ! [A_49,B_50] : k3_xboole_0(k2_tarski(A_49,B_50),k1_tarski(A_49)) = k5_xboole_0(k1_tarski(A_49),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_1356])).

tff(c_2837,plain,(
    ! [A_174,B_175] : k3_xboole_0(k2_tarski(A_174,B_175),k1_tarski(A_174)) = k1_tarski(A_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_4,c_1416])).

tff(c_695,plain,(
    ! [B_99,C_100] : k5_xboole_0(B_99,k5_xboole_0(B_99,C_100)) = C_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_589])).

tff(c_772,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k5_xboole_0(B_107,A_106)) = B_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_695])).

tff(c_835,plain,(
    ! [A_9,B_10] : k5_xboole_0(k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_772])).

tff(c_22,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1413,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(k4_xboole_0(A_14,B_15),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1356])).

tff(c_1431,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_1413])).

tff(c_257,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_248])).

tff(c_1636,plain,(
    ! [A_145,B_146] : k4_xboole_0(A_145,k3_xboole_0(A_145,B_146)) = k4_xboole_0(A_145,B_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_257])).

tff(c_26,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1664,plain,(
    ! [A_145,B_146] : k5_xboole_0(k3_xboole_0(A_145,B_146),k4_xboole_0(A_145,B_146)) = k2_xboole_0(k3_xboole_0(A_145,B_146),A_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_1636,c_26])).

tff(c_1702,plain,(
    ! [A_145,B_146] : k2_xboole_0(k3_xboole_0(A_145,B_146),A_145) = A_145 ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_1664])).

tff(c_2864,plain,(
    ! [A_174,B_175] : k2_xboole_0(k1_tarski(A_174),k2_tarski(A_174,B_175)) = k2_tarski(A_174,B_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_2837,c_1702])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_13283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2864,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.25/3.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/3.25  
% 8.25/3.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/3.25  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.25/3.25  
% 8.25/3.25  %Foreground sorts:
% 8.25/3.25  
% 8.25/3.25  
% 8.25/3.25  %Background operators:
% 8.25/3.25  
% 8.25/3.25  
% 8.25/3.25  %Foreground operators:
% 8.25/3.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.25/3.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.25/3.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.25/3.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.25/3.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.25/3.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.25/3.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.25/3.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.25/3.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.25/3.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.25/3.25  tff('#skF_2', type, '#skF_2': $i).
% 8.25/3.25  tff('#skF_1', type, '#skF_1': $i).
% 8.25/3.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.25/3.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.25/3.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.25/3.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.25/3.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.25/3.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.25/3.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.25/3.25  
% 8.25/3.27  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.25/3.27  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.25/3.27  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.25/3.27  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.25/3.27  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.25/3.27  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.25/3.27  tff(f_69, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.25/3.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.25/3.27  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.25/3.27  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.25/3.27  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.25/3.27  tff(f_72, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 8.25/3.27  tff(c_20, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.25/3.27  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.25/3.27  tff(c_154, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k1_xboole_0 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.25/3.27  tff(c_162, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_154])).
% 8.25/3.27  tff(c_248, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.25/3.27  tff(c_269, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_248])).
% 8.25/3.27  tff(c_275, plain, (![A_79]: (k3_xboole_0(A_79, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_269])).
% 8.25/3.27  tff(c_16, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.25/3.27  tff(c_280, plain, (![A_79]: (k5_xboole_0(A_79, k1_xboole_0)=k4_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_275, c_16])).
% 8.25/3.27  tff(c_382, plain, (![A_83]: (k5_xboole_0(A_83, k1_xboole_0)=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_280])).
% 8.25/3.27  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.25/3.27  tff(c_392, plain, (![A_83]: (k5_xboole_0(k1_xboole_0, A_83)=A_83)), inference(superposition, [status(thm), theory('equality')], [c_382, c_4])).
% 8.25/3.27  tff(c_42, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), k2_tarski(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.25/3.27  tff(c_161, plain, (![A_49, B_50]: (k4_xboole_0(k1_tarski(A_49), k2_tarski(A_49, B_50))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_154])).
% 8.25/3.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.25/3.27  tff(c_209, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.25/3.27  tff(c_1115, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k3_xboole_0(B_128, A_127))=k4_xboole_0(A_127, B_128))), inference(superposition, [status(thm), theory('equality')], [c_2, c_209])).
% 8.25/3.27  tff(c_136, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.25/3.27  tff(c_144, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_136])).
% 8.25/3.27  tff(c_218, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_144, c_209])).
% 8.25/3.27  tff(c_227, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_218])).
% 8.25/3.27  tff(c_535, plain, (![A_89, B_90, C_91]: (k5_xboole_0(k5_xboole_0(A_89, B_90), C_91)=k5_xboole_0(A_89, k5_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.25/3.27  tff(c_589, plain, (![B_6, C_91]: (k5_xboole_0(B_6, k5_xboole_0(B_6, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_227, c_535])).
% 8.25/3.27  tff(c_623, plain, (![B_6, C_91]: (k5_xboole_0(B_6, k5_xboole_0(B_6, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_392, c_589])).
% 8.25/3.27  tff(c_1356, plain, (![A_137, B_138]: (k5_xboole_0(A_137, k4_xboole_0(A_137, B_138))=k3_xboole_0(B_138, A_137))), inference(superposition, [status(thm), theory('equality')], [c_1115, c_623])).
% 8.25/3.27  tff(c_1416, plain, (![A_49, B_50]: (k3_xboole_0(k2_tarski(A_49, B_50), k1_tarski(A_49))=k5_xboole_0(k1_tarski(A_49), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_161, c_1356])).
% 8.25/3.27  tff(c_2837, plain, (![A_174, B_175]: (k3_xboole_0(k2_tarski(A_174, B_175), k1_tarski(A_174))=k1_tarski(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_4, c_1416])).
% 8.25/3.27  tff(c_695, plain, (![B_99, C_100]: (k5_xboole_0(B_99, k5_xboole_0(B_99, C_100))=C_100)), inference(demodulation, [status(thm), theory('equality')], [c_392, c_589])).
% 8.25/3.27  tff(c_772, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k5_xboole_0(B_107, A_106))=B_107)), inference(superposition, [status(thm), theory('equality')], [c_4, c_695])).
% 8.25/3.27  tff(c_835, plain, (![A_9, B_10]: (k5_xboole_0(k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=A_9)), inference(superposition, [status(thm), theory('equality')], [c_16, c_772])).
% 8.25/3.27  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.25/3.27  tff(c_1413, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(k4_xboole_0(A_14, B_15), A_14))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1356])).
% 8.25/3.27  tff(c_1431, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_1413])).
% 8.25/3.27  tff(c_257, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_248])).
% 8.25/3.27  tff(c_1636, plain, (![A_145, B_146]: (k4_xboole_0(A_145, k3_xboole_0(A_145, B_146))=k4_xboole_0(A_145, B_146))), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_257])).
% 8.25/3.27  tff(c_26, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.25/3.27  tff(c_1664, plain, (![A_145, B_146]: (k5_xboole_0(k3_xboole_0(A_145, B_146), k4_xboole_0(A_145, B_146))=k2_xboole_0(k3_xboole_0(A_145, B_146), A_145))), inference(superposition, [status(thm), theory('equality')], [c_1636, c_26])).
% 8.25/3.27  tff(c_1702, plain, (![A_145, B_146]: (k2_xboole_0(k3_xboole_0(A_145, B_146), A_145)=A_145)), inference(demodulation, [status(thm), theory('equality')], [c_835, c_1664])).
% 8.25/3.27  tff(c_2864, plain, (![A_174, B_175]: (k2_xboole_0(k1_tarski(A_174), k2_tarski(A_174, B_175))=k2_tarski(A_174, B_175))), inference(superposition, [status(thm), theory('equality')], [c_2837, c_1702])).
% 8.25/3.27  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.25/3.27  tff(c_13283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2864, c_44])).
% 8.25/3.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/3.27  
% 8.25/3.27  Inference rules
% 8.25/3.27  ----------------------
% 8.25/3.27  #Ref     : 0
% 8.25/3.27  #Sup     : 3303
% 8.25/3.27  #Fact    : 0
% 8.25/3.27  #Define  : 0
% 8.25/3.27  #Split   : 0
% 8.25/3.27  #Chain   : 0
% 8.25/3.27  #Close   : 0
% 8.25/3.27  
% 8.25/3.27  Ordering : KBO
% 8.25/3.27  
% 8.25/3.27  Simplification rules
% 8.25/3.27  ----------------------
% 8.25/3.27  #Subsume      : 219
% 8.25/3.27  #Demod        : 3807
% 8.25/3.27  #Tautology    : 1912
% 8.25/3.27  #SimpNegUnit  : 0
% 8.25/3.27  #BackRed      : 1
% 8.25/3.27  
% 8.25/3.27  #Partial instantiations: 0
% 8.25/3.27  #Strategies tried      : 1
% 8.25/3.27  
% 8.25/3.27  Timing (in seconds)
% 8.25/3.27  ----------------------
% 8.25/3.27  Preprocessing        : 0.33
% 8.25/3.27  Parsing              : 0.18
% 8.25/3.27  CNF conversion       : 0.02
% 8.25/3.27  Main loop            : 2.17
% 8.25/3.27  Inferencing          : 0.47
% 8.25/3.27  Reduction            : 1.31
% 8.25/3.27  Demodulation         : 1.19
% 8.25/3.27  BG Simplification    : 0.07
% 8.25/3.27  Subsumption          : 0.24
% 8.25/3.27  Abstraction          : 0.10
% 8.25/3.27  MUC search           : 0.00
% 8.25/3.27  Cooper               : 0.00
% 8.25/3.27  Total                : 2.53
% 8.25/3.27  Index Insertion      : 0.00
% 8.25/3.27  Index Deletion       : 0.00
% 8.25/3.28  Index Matching       : 0.00
% 8.25/3.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
