%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:28 EST 2020

% Result     : Theorem 9.99s
% Output     : CNFRefutation 9.99s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 167 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   68 ( 163 expanded)
%              Number of equality atoms :   51 ( 140 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_139,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_151,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_92,plain,(
    ! [B_34,A_35] : k5_xboole_0(B_34,A_35) = k5_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [A_35] : k5_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_196,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1479,plain,(
    ! [B_94,A_95] : k5_xboole_0(B_94,k3_xboole_0(A_95,B_94)) = k4_xboole_0(B_94,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_196])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_222,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_196])).

tff(c_225,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_222])).

tff(c_684,plain,(
    ! [A_67,B_68,C_69] : k5_xboole_0(k5_xboole_0(A_67,B_68),C_69) = k5_xboole_0(A_67,k5_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_728,plain,(
    ! [A_10,C_69] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_69)) = k5_xboole_0(k1_xboole_0,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_684])).

tff(c_769,plain,(
    ! [A_10,C_69] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_69)) = C_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_728])).

tff(c_2990,plain,(
    ! [B_111,A_112] : k5_xboole_0(B_111,k4_xboole_0(B_111,A_112)) = k3_xboole_0(A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_1479,c_769])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1935,plain,(
    ! [C_99,A_100,B_101] : k5_xboole_0(C_99,k5_xboole_0(A_100,B_101)) = k5_xboole_0(A_100,k5_xboole_0(B_101,C_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_4])).

tff(c_2218,plain,(
    ! [A_35,C_99] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_35,C_99)) = k5_xboole_0(C_99,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1935])).

tff(c_2999,plain,(
    ! [B_111,A_112] : k5_xboole_0(k4_xboole_0(B_111,A_112),B_111) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_112,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_2218])).

tff(c_3076,plain,(
    ! [B_111,A_112] : k5_xboole_0(k4_xboole_0(B_111,A_112),B_111) = k3_xboole_0(A_112,B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2999])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1233,plain,(
    ! [A_86,B_87] : k3_xboole_0(k4_xboole_0(A_86,B_87),A_86) = k4_xboole_0(A_86,B_87) ),
    inference(resolution,[status(thm)],[c_16,c_139])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1243,plain,(
    ! [A_86,B_87] : k5_xboole_0(k4_xboole_0(A_86,B_87),k4_xboole_0(A_86,B_87)) = k4_xboole_0(k4_xboole_0(A_86,B_87),A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_1233,c_6])).

tff(c_1290,plain,(
    ! [A_88,B_89] : k4_xboole_0(k4_xboole_0(A_88,B_89),A_88) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_1243])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1316,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = k5_xboole_0(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1290,c_24])).

tff(c_1361,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1316])).

tff(c_2485,plain,(
    ! [A_103,C_104] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_103,C_104)) = k5_xboole_0(C_104,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1935])).

tff(c_2602,plain,(
    ! [B_23,A_22] : k5_xboole_0(k4_xboole_0(B_23,A_22),A_22) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2485])).

tff(c_2655,plain,(
    ! [B_23,A_22] : k5_xboole_0(k4_xboole_0(B_23,A_22),A_22) = k2_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2602])).

tff(c_219,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_196])).

tff(c_2576,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_2485])).

tff(c_2648,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2576])).

tff(c_7243,plain,(
    ! [A_155,B_156,C_157] : k5_xboole_0(A_155,k5_xboole_0(k3_xboole_0(A_155,B_156),C_157)) = k5_xboole_0(k4_xboole_0(A_155,B_156),C_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_684])).

tff(c_7378,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2648,c_7243])).

tff(c_7524,plain,(
    ! [B_158,A_159] : k2_xboole_0(B_158,A_159) = k2_xboole_0(A_159,B_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2655,c_24,c_7378])).

tff(c_773,plain,(
    ! [A_70,C_71] : k5_xboole_0(A_70,k5_xboole_0(A_70,C_71)) = C_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_728])).

tff(c_806,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k4_xboole_0(B_23,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_773])).

tff(c_11683,plain,(
    ! [B_196,A_197] : k5_xboole_0(B_196,k2_xboole_0(A_197,B_196)) = k4_xboole_0(A_197,B_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_7524,c_806])).

tff(c_11807,plain,(
    ! [A_88,B_89] : k5_xboole_0(k4_xboole_0(A_88,B_89),A_88) = k4_xboole_0(A_88,k4_xboole_0(A_88,B_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_11683])).

tff(c_14182,plain,(
    ! [A_214,B_215] : k4_xboole_0(A_214,k4_xboole_0(A_214,B_215)) = k3_xboole_0(B_215,A_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_11807])).

tff(c_570,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(A_60,B_61)
      | ~ r1_tarski(A_60,k4_xboole_0(B_61,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_602,plain,(
    ! [B_61,C_62,B_15] : r1_tarski(k4_xboole_0(k4_xboole_0(B_61,C_62),B_15),B_61) ),
    inference(resolution,[status(thm)],[c_16,c_570])).

tff(c_18608,plain,(
    ! [B_254,A_255,B_256] : r1_tarski(k4_xboole_0(k3_xboole_0(B_254,A_255),B_256),A_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_14182,c_602])).

tff(c_18672,plain,(
    ! [B_256] : r1_tarski(k4_xboole_0('#skF_1',B_256),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_18608])).

tff(c_26,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18672,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.99/4.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/4.17  
% 9.99/4.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/4.17  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.99/4.17  
% 9.99/4.17  %Foreground sorts:
% 9.99/4.17  
% 9.99/4.17  
% 9.99/4.17  %Background operators:
% 9.99/4.17  
% 9.99/4.17  
% 9.99/4.17  %Foreground operators:
% 9.99/4.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.99/4.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.99/4.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.99/4.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.99/4.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.99/4.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.99/4.17  tff('#skF_2', type, '#skF_2': $i).
% 9.99/4.17  tff('#skF_3', type, '#skF_3': $i).
% 9.99/4.17  tff('#skF_1', type, '#skF_1': $i).
% 9.99/4.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.99/4.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.99/4.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.99/4.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.99/4.17  
% 9.99/4.18  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 9.99/4.18  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.99/4.18  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.99/4.18  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 9.99/4.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.99/4.18  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.99/4.18  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 9.99/4.18  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 9.99/4.18  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.99/4.18  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.99/4.18  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.99/4.18  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 9.99/4.18  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.99/4.18  tff(c_139, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.99/4.18  tff(c_151, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_28, c_139])).
% 9.99/4.18  tff(c_92, plain, (![B_34, A_35]: (k5_xboole_0(B_34, A_35)=k5_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.99/4.18  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.99/4.18  tff(c_108, plain, (![A_35]: (k5_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_92, c_20])).
% 9.99/4.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.99/4.18  tff(c_196, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.99/4.18  tff(c_1479, plain, (![B_94, A_95]: (k5_xboole_0(B_94, k3_xboole_0(A_95, B_94))=k4_xboole_0(B_94, A_95))), inference(superposition, [status(thm), theory('equality')], [c_2, c_196])).
% 9.99/4.18  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.99/4.18  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.99/4.18  tff(c_222, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k5_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_196])).
% 9.99/4.18  tff(c_225, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_222])).
% 9.99/4.18  tff(c_684, plain, (![A_67, B_68, C_69]: (k5_xboole_0(k5_xboole_0(A_67, B_68), C_69)=k5_xboole_0(A_67, k5_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.99/4.18  tff(c_728, plain, (![A_10, C_69]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_69))=k5_xboole_0(k1_xboole_0, C_69))), inference(superposition, [status(thm), theory('equality')], [c_225, c_684])).
% 9.99/4.18  tff(c_769, plain, (![A_10, C_69]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_69))=C_69)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_728])).
% 9.99/4.18  tff(c_2990, plain, (![B_111, A_112]: (k5_xboole_0(B_111, k4_xboole_0(B_111, A_112))=k3_xboole_0(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_1479, c_769])).
% 9.99/4.18  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.99/4.18  tff(c_1935, plain, (![C_99, A_100, B_101]: (k5_xboole_0(C_99, k5_xboole_0(A_100, B_101))=k5_xboole_0(A_100, k5_xboole_0(B_101, C_99)))), inference(superposition, [status(thm), theory('equality')], [c_684, c_4])).
% 9.99/4.18  tff(c_2218, plain, (![A_35, C_99]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_35, C_99))=k5_xboole_0(C_99, A_35))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1935])).
% 9.99/4.18  tff(c_2999, plain, (![B_111, A_112]: (k5_xboole_0(k4_xboole_0(B_111, A_112), B_111)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_112, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_2218])).
% 9.99/4.18  tff(c_3076, plain, (![B_111, A_112]: (k5_xboole_0(k4_xboole_0(B_111, A_112), B_111)=k3_xboole_0(A_112, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2999])).
% 9.99/4.18  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.99/4.18  tff(c_1233, plain, (![A_86, B_87]: (k3_xboole_0(k4_xboole_0(A_86, B_87), A_86)=k4_xboole_0(A_86, B_87))), inference(resolution, [status(thm)], [c_16, c_139])).
% 9.99/4.18  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.99/4.18  tff(c_1243, plain, (![A_86, B_87]: (k5_xboole_0(k4_xboole_0(A_86, B_87), k4_xboole_0(A_86, B_87))=k4_xboole_0(k4_xboole_0(A_86, B_87), A_86))), inference(superposition, [status(thm), theory('equality')], [c_1233, c_6])).
% 9.99/4.18  tff(c_1290, plain, (![A_88, B_89]: (k4_xboole_0(k4_xboole_0(A_88, B_89), A_88)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_225, c_1243])).
% 9.99/4.18  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.99/4.18  tff(c_1316, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(A_88, B_89))=k5_xboole_0(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1290, c_24])).
% 9.99/4.18  tff(c_1361, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(A_88, B_89))=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1316])).
% 9.99/4.18  tff(c_2485, plain, (![A_103, C_104]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_103, C_104))=k5_xboole_0(C_104, A_103))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1935])).
% 9.99/4.18  tff(c_2602, plain, (![B_23, A_22]: (k5_xboole_0(k4_xboole_0(B_23, A_22), A_22)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2485])).
% 9.99/4.18  tff(c_2655, plain, (![B_23, A_22]: (k5_xboole_0(k4_xboole_0(B_23, A_22), A_22)=k2_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2602])).
% 9.99/4.18  tff(c_219, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_196])).
% 9.99/4.18  tff(c_2576, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_2485])).
% 9.99/4.18  tff(c_2648, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2576])).
% 9.99/4.18  tff(c_7243, plain, (![A_155, B_156, C_157]: (k5_xboole_0(A_155, k5_xboole_0(k3_xboole_0(A_155, B_156), C_157))=k5_xboole_0(k4_xboole_0(A_155, B_156), C_157))), inference(superposition, [status(thm), theory('equality')], [c_6, c_684])).
% 9.99/4.18  tff(c_7378, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2648, c_7243])).
% 9.99/4.18  tff(c_7524, plain, (![B_158, A_159]: (k2_xboole_0(B_158, A_159)=k2_xboole_0(A_159, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_2655, c_24, c_7378])).
% 9.99/4.18  tff(c_773, plain, (![A_70, C_71]: (k5_xboole_0(A_70, k5_xboole_0(A_70, C_71))=C_71)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_728])).
% 9.99/4.18  tff(c_806, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k4_xboole_0(B_23, A_22))), inference(superposition, [status(thm), theory('equality')], [c_24, c_773])).
% 9.99/4.18  tff(c_11683, plain, (![B_196, A_197]: (k5_xboole_0(B_196, k2_xboole_0(A_197, B_196))=k4_xboole_0(A_197, B_196))), inference(superposition, [status(thm), theory('equality')], [c_7524, c_806])).
% 9.99/4.18  tff(c_11807, plain, (![A_88, B_89]: (k5_xboole_0(k4_xboole_0(A_88, B_89), A_88)=k4_xboole_0(A_88, k4_xboole_0(A_88, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_1361, c_11683])).
% 9.99/4.18  tff(c_14182, plain, (![A_214, B_215]: (k4_xboole_0(A_214, k4_xboole_0(A_214, B_215))=k3_xboole_0(B_215, A_214))), inference(demodulation, [status(thm), theory('equality')], [c_3076, c_11807])).
% 9.99/4.18  tff(c_570, plain, (![A_60, B_61, C_62]: (r1_tarski(A_60, B_61) | ~r1_tarski(A_60, k4_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.99/4.18  tff(c_602, plain, (![B_61, C_62, B_15]: (r1_tarski(k4_xboole_0(k4_xboole_0(B_61, C_62), B_15), B_61))), inference(resolution, [status(thm)], [c_16, c_570])).
% 9.99/4.18  tff(c_18608, plain, (![B_254, A_255, B_256]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_254, A_255), B_256), A_255))), inference(superposition, [status(thm), theory('equality')], [c_14182, c_602])).
% 9.99/4.18  tff(c_18672, plain, (![B_256]: (r1_tarski(k4_xboole_0('#skF_1', B_256), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_18608])).
% 9.99/4.18  tff(c_26, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.99/4.18  tff(c_18706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18672, c_26])).
% 9.99/4.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/4.18  
% 9.99/4.18  Inference rules
% 9.99/4.18  ----------------------
% 9.99/4.18  #Ref     : 0
% 9.99/4.18  #Sup     : 4638
% 9.99/4.18  #Fact    : 0
% 9.99/4.18  #Define  : 0
% 9.99/4.18  #Split   : 0
% 9.99/4.18  #Chain   : 0
% 9.99/4.18  #Close   : 0
% 9.99/4.18  
% 9.99/4.18  Ordering : KBO
% 9.99/4.18  
% 9.99/4.18  Simplification rules
% 9.99/4.18  ----------------------
% 9.99/4.18  #Subsume      : 241
% 9.99/4.18  #Demod        : 5762
% 9.99/4.18  #Tautology    : 2466
% 9.99/4.18  #SimpNegUnit  : 0
% 9.99/4.18  #BackRed      : 2
% 9.99/4.18  
% 9.99/4.18  #Partial instantiations: 0
% 9.99/4.18  #Strategies tried      : 1
% 9.99/4.18  
% 9.99/4.18  Timing (in seconds)
% 9.99/4.18  ----------------------
% 9.99/4.19  Preprocessing        : 0.29
% 9.99/4.19  Parsing              : 0.16
% 9.99/4.19  CNF conversion       : 0.02
% 9.99/4.19  Main loop            : 3.08
% 9.99/4.19  Inferencing          : 0.57
% 9.99/4.19  Reduction            : 1.98
% 9.99/4.19  Demodulation         : 1.83
% 9.99/4.19  BG Simplification    : 0.08
% 9.99/4.19  Subsumption          : 0.34
% 9.99/4.19  Abstraction          : 0.11
% 9.99/4.19  MUC search           : 0.00
% 9.99/4.19  Cooper               : 0.00
% 9.99/4.19  Total                : 3.40
% 9.99/4.19  Index Insertion      : 0.00
% 9.99/4.19  Index Deletion       : 0.00
% 9.99/4.19  Index Matching       : 0.00
% 9.99/4.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
