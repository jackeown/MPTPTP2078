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
% DateTime   : Thu Dec  3 09:44:57 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 159 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :   78 ( 166 expanded)
%              Number of equality atoms :   64 ( 130 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_202,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_215,plain,(
    ! [B_20,A_19] : k4_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = B_20 ),
    inference(resolution,[status(thm)],[c_187,c_202])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),C_17) = k3_xboole_0(A_15,k4_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_371,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_423,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_371])).

tff(c_431,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_423])).

tff(c_1292,plain,(
    ! [A_95,B_96] : k4_xboole_0(k4_xboole_0(A_95,B_96),B_96) = k4_xboole_0(A_95,B_96) ),
    inference(resolution,[status(thm)],[c_24,c_202])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1313,plain,(
    ! [A_95,B_96] : k4_xboole_0(k4_xboole_0(A_95,B_96),k4_xboole_0(A_95,B_96)) = k3_xboole_0(k4_xboole_0(A_95,B_96),B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_18])).

tff(c_1381,plain,(
    ! [A_97,B_98] : k3_xboole_0(k4_xboole_0(A_97,B_98),B_98) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_1313])).

tff(c_1424,plain,(
    ! [B_20,A_19] : k3_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_1381])).

tff(c_576,plain,(
    ! [A_71,B_72,C_73] : k4_xboole_0(k3_xboole_0(A_71,B_72),C_73) = k3_xboole_0(A_71,k4_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6447,plain,(
    ! [C_203,A_204,B_205] : k5_xboole_0(C_203,k3_xboole_0(A_204,k4_xboole_0(B_205,C_203))) = k2_xboole_0(C_203,k3_xboole_0(A_204,B_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_34])).

tff(c_6537,plain,(
    ! [B_20,A_19] : k2_xboole_0(B_20,k3_xboole_0(B_20,A_19)) = k5_xboole_0(B_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_6447])).

tff(c_6605,plain,(
    ! [B_206,A_207] : k2_xboole_0(B_206,k3_xboole_0(B_206,A_207)) = B_206 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6537])).

tff(c_83,plain,(
    ! [B_35,A_36] : k5_xboole_0(B_35,A_36) = k5_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_83])).

tff(c_723,plain,(
    ! [A_76,B_77,C_78] : k5_xboole_0(k5_xboole_0(A_76,B_77),C_78) = k5_xboole_0(A_76,k5_xboole_0(B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_787,plain,(
    ! [A_26,C_78] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_78)) = k5_xboole_0(k1_xboole_0,C_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_723])).

tff(c_802,plain,(
    ! [A_79,C_80] : k5_xboole_0(A_79,k5_xboole_0(A_79,C_80)) = C_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_787])).

tff(c_835,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = k4_xboole_0(B_28,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_802])).

tff(c_2058,plain,(
    ! [C_121,A_122,B_123] : k5_xboole_0(C_121,k5_xboole_0(A_122,B_123)) = k5_xboole_0(A_122,k5_xboole_0(B_123,C_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_2])).

tff(c_2390,plain,(
    ! [A_124,C_125] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_124,C_125)) = k5_xboole_0(C_125,A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_2058])).

tff(c_2457,plain,(
    ! [A_27,B_28] : k5_xboole_0(k2_xboole_0(A_27,B_28),A_27) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_28,A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_2390])).

tff(c_2518,plain,(
    ! [A_27,B_28] : k5_xboole_0(k2_xboole_0(A_27,B_28),A_27) = k4_xboole_0(B_28,A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2457])).

tff(c_6615,plain,(
    ! [B_206,A_207] : k4_xboole_0(k3_xboole_0(B_206,A_207),B_206) = k5_xboole_0(B_206,B_206) ),
    inference(superposition,[status(thm),theory(equality)],[c_6605,c_2518])).

tff(c_6709,plain,(
    ! [B_208,A_209] : k4_xboole_0(k3_xboole_0(B_208,A_209),B_208) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6615])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_295,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,B_54) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_299,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_295])).

tff(c_6922,plain,(
    ! [B_208,A_209] : k2_xboole_0(k3_xboole_0(B_208,A_209),B_208) = B_208 ),
    inference(superposition,[status(thm),theory(equality)],[c_6709,c_299])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2483,plain,(
    ! [B_28,A_27] : k5_xboole_0(k4_xboole_0(B_28,A_27),A_27) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2390])).

tff(c_3550,plain,(
    ! [B_146,A_147] : k5_xboole_0(k4_xboole_0(B_146,A_147),A_147) = k2_xboole_0(A_147,B_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2483])).

tff(c_3630,plain,(
    ! [B_20,A_19] : k5_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k2_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_3550])).

tff(c_8072,plain,(
    ! [A_225,B_226] : k2_xboole_0(k4_xboole_0(A_225,B_226),B_226) = k2_xboole_0(B_226,A_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3630])).

tff(c_8136,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k2_xboole_0(k3_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8072])).

tff(c_16806,plain,(
    ! [A_314,B_315] : k2_xboole_0(k4_xboole_0(A_314,B_315),k3_xboole_0(A_314,B_315)) = A_314 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6922,c_8136])).

tff(c_867,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k5_xboole_0(B_82,A_81)) = B_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_802])).

tff(c_914,plain,(
    ! [B_28,A_27] : k5_xboole_0(k4_xboole_0(B_28,A_27),k2_xboole_0(A_27,B_28)) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_867])).

tff(c_16821,plain,(
    ! [A_314,B_315] : k5_xboole_0(k4_xboole_0(k3_xboole_0(A_314,B_315),k4_xboole_0(A_314,B_315)),A_314) = k4_xboole_0(A_314,B_315) ),
    inference(superposition,[status(thm),theory(equality)],[c_16806,c_914])).

tff(c_16973,plain,(
    ! [A_314,B_315] : k5_xboole_0(A_314,k3_xboole_0(A_314,B_315)) = k4_xboole_0(A_314,B_315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_2,c_20,c_16821])).

tff(c_36,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16973,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.63/3.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/3.00  
% 7.80/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/3.01  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 7.80/3.01  
% 7.80/3.01  %Foreground sorts:
% 7.80/3.01  
% 7.80/3.01  
% 7.80/3.01  %Background operators:
% 7.80/3.01  
% 7.80/3.01  
% 7.80/3.01  %Foreground operators:
% 7.80/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.80/3.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.80/3.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.80/3.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.80/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.80/3.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.80/3.01  tff('#skF_2', type, '#skF_2': $i).
% 7.80/3.01  tff('#skF_1', type, '#skF_1': $i).
% 7.80/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.80/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.80/3.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.80/3.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.80/3.01  
% 7.80/3.02  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.80/3.02  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.80/3.02  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.80/3.02  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.80/3.02  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.80/3.02  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.80/3.02  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.80/3.02  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.80/3.02  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.80/3.02  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.80/3.02  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.80/3.02  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.80/3.02  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.80/3.02  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.80/3.02  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.80/3.02  tff(f_66, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.80/3.02  tff(c_24, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.80/3.02  tff(c_181, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.80/3.02  tff(c_187, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_24, c_181])).
% 7.80/3.02  tff(c_202, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.80/3.02  tff(c_215, plain, (![B_20, A_19]: (k4_xboole_0(B_20, k4_xboole_0(A_19, B_20))=B_20)), inference(resolution, [status(thm)], [c_187, c_202])).
% 7.80/3.02  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.80/3.02  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k3_xboole_0(A_15, B_16), C_17)=k3_xboole_0(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.80/3.02  tff(c_32, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.80/3.02  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.80/3.02  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.80/3.02  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.80/3.02  tff(c_371, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.80/3.02  tff(c_423, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_371])).
% 7.80/3.02  tff(c_431, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_423])).
% 7.80/3.02  tff(c_1292, plain, (![A_95, B_96]: (k4_xboole_0(k4_xboole_0(A_95, B_96), B_96)=k4_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_24, c_202])).
% 7.80/3.02  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.80/3.02  tff(c_1313, plain, (![A_95, B_96]: (k4_xboole_0(k4_xboole_0(A_95, B_96), k4_xboole_0(A_95, B_96))=k3_xboole_0(k4_xboole_0(A_95, B_96), B_96))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_18])).
% 7.80/3.02  tff(c_1381, plain, (![A_97, B_98]: (k3_xboole_0(k4_xboole_0(A_97, B_98), B_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_431, c_1313])).
% 7.80/3.02  tff(c_1424, plain, (![B_20, A_19]: (k3_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_215, c_1381])).
% 7.80/3.02  tff(c_576, plain, (![A_71, B_72, C_73]: (k4_xboole_0(k3_xboole_0(A_71, B_72), C_73)=k3_xboole_0(A_71, k4_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.80/3.02  tff(c_34, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.80/3.02  tff(c_6447, plain, (![C_203, A_204, B_205]: (k5_xboole_0(C_203, k3_xboole_0(A_204, k4_xboole_0(B_205, C_203)))=k2_xboole_0(C_203, k3_xboole_0(A_204, B_205)))), inference(superposition, [status(thm), theory('equality')], [c_576, c_34])).
% 7.80/3.02  tff(c_6537, plain, (![B_20, A_19]: (k2_xboole_0(B_20, k3_xboole_0(B_20, A_19))=k5_xboole_0(B_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1424, c_6447])).
% 7.80/3.02  tff(c_6605, plain, (![B_206, A_207]: (k2_xboole_0(B_206, k3_xboole_0(B_206, A_207))=B_206)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6537])).
% 7.80/3.02  tff(c_83, plain, (![B_35, A_36]: (k5_xboole_0(B_35, A_36)=k5_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.80/3.02  tff(c_118, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, A_18)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_22, c_83])).
% 7.80/3.02  tff(c_723, plain, (![A_76, B_77, C_78]: (k5_xboole_0(k5_xboole_0(A_76, B_77), C_78)=k5_xboole_0(A_76, k5_xboole_0(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.80/3.02  tff(c_787, plain, (![A_26, C_78]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_78))=k5_xboole_0(k1_xboole_0, C_78))), inference(superposition, [status(thm), theory('equality')], [c_32, c_723])).
% 7.80/3.02  tff(c_802, plain, (![A_79, C_80]: (k5_xboole_0(A_79, k5_xboole_0(A_79, C_80))=C_80)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_787])).
% 7.80/3.02  tff(c_835, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k2_xboole_0(A_27, B_28))=k4_xboole_0(B_28, A_27))), inference(superposition, [status(thm), theory('equality')], [c_34, c_802])).
% 7.80/3.02  tff(c_2058, plain, (![C_121, A_122, B_123]: (k5_xboole_0(C_121, k5_xboole_0(A_122, B_123))=k5_xboole_0(A_122, k5_xboole_0(B_123, C_121)))), inference(superposition, [status(thm), theory('equality')], [c_723, c_2])).
% 7.80/3.02  tff(c_2390, plain, (![A_124, C_125]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_124, C_125))=k5_xboole_0(C_125, A_124))), inference(superposition, [status(thm), theory('equality')], [c_118, c_2058])).
% 7.80/3.02  tff(c_2457, plain, (![A_27, B_28]: (k5_xboole_0(k2_xboole_0(A_27, B_28), A_27)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_28, A_27)))), inference(superposition, [status(thm), theory('equality')], [c_835, c_2390])).
% 7.80/3.02  tff(c_2518, plain, (![A_27, B_28]: (k5_xboole_0(k2_xboole_0(A_27, B_28), A_27)=k4_xboole_0(B_28, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2457])).
% 7.80/3.02  tff(c_6615, plain, (![B_206, A_207]: (k4_xboole_0(k3_xboole_0(B_206, A_207), B_206)=k5_xboole_0(B_206, B_206))), inference(superposition, [status(thm), theory('equality')], [c_6605, c_2518])).
% 7.80/3.02  tff(c_6709, plain, (![B_208, A_209]: (k4_xboole_0(k3_xboole_0(B_208, A_209), B_208)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6615])).
% 7.80/3.02  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.80/3.02  tff(c_295, plain, (![A_53, B_54]: (k2_xboole_0(A_53, B_54)=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.80/3.02  tff(c_299, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_295])).
% 7.80/3.02  tff(c_6922, plain, (![B_208, A_209]: (k2_xboole_0(k3_xboole_0(B_208, A_209), B_208)=B_208)), inference(superposition, [status(thm), theory('equality')], [c_6709, c_299])).
% 7.80/3.02  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/3.02  tff(c_2483, plain, (![B_28, A_27]: (k5_xboole_0(k4_xboole_0(B_28, A_27), A_27)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2390])).
% 7.80/3.02  tff(c_3550, plain, (![B_146, A_147]: (k5_xboole_0(k4_xboole_0(B_146, A_147), A_147)=k2_xboole_0(A_147, B_146))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2483])).
% 7.80/3.02  tff(c_3630, plain, (![B_20, A_19]: (k5_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k2_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(superposition, [status(thm), theory('equality')], [c_215, c_3550])).
% 7.80/3.02  tff(c_8072, plain, (![A_225, B_226]: (k2_xboole_0(k4_xboole_0(A_225, B_226), B_226)=k2_xboole_0(B_226, A_225))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3630])).
% 7.80/3.02  tff(c_8136, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k2_xboole_0(k3_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8072])).
% 7.80/3.02  tff(c_16806, plain, (![A_314, B_315]: (k2_xboole_0(k4_xboole_0(A_314, B_315), k3_xboole_0(A_314, B_315))=A_314)), inference(demodulation, [status(thm), theory('equality')], [c_6922, c_8136])).
% 7.80/3.02  tff(c_867, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k5_xboole_0(B_82, A_81))=B_82)), inference(superposition, [status(thm), theory('equality')], [c_2, c_802])).
% 7.80/3.02  tff(c_914, plain, (![B_28, A_27]: (k5_xboole_0(k4_xboole_0(B_28, A_27), k2_xboole_0(A_27, B_28))=A_27)), inference(superposition, [status(thm), theory('equality')], [c_34, c_867])).
% 7.80/3.02  tff(c_16821, plain, (![A_314, B_315]: (k5_xboole_0(k4_xboole_0(k3_xboole_0(A_314, B_315), k4_xboole_0(A_314, B_315)), A_314)=k4_xboole_0(A_314, B_315))), inference(superposition, [status(thm), theory('equality')], [c_16806, c_914])).
% 7.80/3.02  tff(c_16973, plain, (![A_314, B_315]: (k5_xboole_0(A_314, k3_xboole_0(A_314, B_315))=k4_xboole_0(A_314, B_315))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_2, c_20, c_16821])).
% 7.80/3.02  tff(c_36, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.80/3.02  tff(c_18178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16973, c_36])).
% 7.80/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/3.02  
% 7.80/3.02  Inference rules
% 7.80/3.02  ----------------------
% 7.80/3.02  #Ref     : 0
% 7.80/3.02  #Sup     : 4554
% 7.80/3.02  #Fact    : 0
% 7.80/3.02  #Define  : 0
% 7.80/3.02  #Split   : 0
% 7.80/3.02  #Chain   : 0
% 7.80/3.02  #Close   : 0
% 7.80/3.02  
% 7.80/3.02  Ordering : KBO
% 7.80/3.02  
% 7.80/3.02  Simplification rules
% 7.80/3.02  ----------------------
% 7.80/3.02  #Subsume      : 103
% 7.80/3.02  #Demod        : 4686
% 7.80/3.02  #Tautology    : 3175
% 7.80/3.02  #SimpNegUnit  : 0
% 7.80/3.02  #BackRed      : 1
% 7.80/3.02  
% 7.80/3.02  #Partial instantiations: 0
% 7.80/3.02  #Strategies tried      : 1
% 7.80/3.02  
% 7.80/3.02  Timing (in seconds)
% 7.80/3.02  ----------------------
% 7.80/3.02  Preprocessing        : 0.28
% 7.80/3.02  Parsing              : 0.15
% 7.80/3.02  CNF conversion       : 0.02
% 7.80/3.02  Main loop            : 1.93
% 7.80/3.02  Inferencing          : 0.52
% 7.80/3.02  Reduction            : 0.97
% 7.80/3.02  Demodulation         : 0.84
% 7.80/3.02  BG Simplification    : 0.06
% 7.80/3.02  Subsumption          : 0.29
% 7.80/3.02  Abstraction          : 0.11
% 7.80/3.02  MUC search           : 0.00
% 7.80/3.02  Cooper               : 0.00
% 7.80/3.02  Total                : 2.25
% 7.80/3.03  Index Insertion      : 0.00
% 7.80/3.03  Index Deletion       : 0.00
% 7.80/3.03  Index Matching       : 0.00
% 7.80/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
