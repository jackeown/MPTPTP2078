%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:07 EST 2020

% Result     : Theorem 9.45s
% Output     : CNFRefutation 9.52s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 681 expanded)
%              Number of leaves         :   31 ( 243 expanded)
%              Depth                    :   20
%              Number of atoms          :   72 ( 748 expanded)
%              Number of equality atoms :   62 ( 626 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_321,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k4_xboole_0(B_79,A_78)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_345,plain,(
    ! [A_80] : k5_xboole_0(k1_xboole_0,A_80) = k2_xboole_0(k1_xboole_0,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_321])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_362,plain,(
    ! [A_80] : k5_xboole_0(A_80,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_4])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_147,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_175,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_175])).

tff(c_299,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_311,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_299])).

tff(c_386,plain,(
    ! [B_81] : k5_xboole_0(B_81,B_81) = k3_xboole_0(B_81,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_311])).

tff(c_342,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k2_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_321])).

tff(c_393,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_342])).

tff(c_402,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_393])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_641,plain,(
    ! [B_93] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_93)) = k4_xboole_0(k1_xboole_0,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_12])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_774,plain,(
    ! [B_106] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_106)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_146])).

tff(c_356,plain,(
    ! [B_8] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_8)) = k4_xboole_0(k1_xboole_0,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_12])).

tff(c_781,plain,(
    ! [B_106] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_106)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_356])).

tff(c_851,plain,(
    ! [B_108] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_108)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_781])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_919,plain,(
    ! [B_109] : k3_xboole_0(k1_xboole_0,B_109) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_314,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_299])).

tff(c_927,plain,(
    ! [B_109] : k5_xboole_0(B_109,k1_xboole_0) = k4_xboole_0(B_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_314])).

tff(c_969,plain,(
    ! [B_109] : k2_xboole_0(k1_xboole_0,B_109) = B_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_16,c_927])).

tff(c_1114,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_342])).

tff(c_24,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_477,plain,(
    ! [A_86,B_87,C_88] : k5_xboole_0(k5_xboole_0(A_86,B_87),C_88) = k5_xboole_0(A_86,k5_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2036,plain,(
    ! [B_149,A_150,B_151] : k5_xboole_0(B_149,k5_xboole_0(A_150,B_151)) = k5_xboole_0(A_150,k5_xboole_0(B_151,B_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_477])).

tff(c_2513,plain,(
    ! [A_156,B_157] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_156,B_157)) = k5_xboole_0(B_157,A_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_2036])).

tff(c_2624,plain,(
    ! [B_20,A_19] : k5_xboole_0(k4_xboole_0(B_20,A_19),A_19) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2513])).

tff(c_2661,plain,(
    ! [B_20,A_19] : k5_xboole_0(k4_xboole_0(B_20,A_19),A_19) = k2_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_2624])).

tff(c_2618,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_2513])).

tff(c_2660,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_2618])).

tff(c_6318,plain,(
    ! [A_230,B_231,C_232] : k5_xboole_0(A_230,k5_xboole_0(k3_xboole_0(A_230,B_231),C_232)) = k5_xboole_0(k4_xboole_0(A_230,B_231),C_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_477])).

tff(c_6410,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2660,c_6318])).

tff(c_6527,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_24,c_6410])).

tff(c_962,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_919])).

tff(c_320,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k3_xboole_0(B_6,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_311])).

tff(c_1046,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_320])).

tff(c_40,plain,(
    ! [A_49,B_50] : r1_tarski(k1_tarski(A_49),k2_tarski(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_145,plain,(
    ! [A_49,B_50] : k3_xboole_0(k1_tarski(A_49),k2_tarski(A_49,B_50)) = k1_tarski(A_49) ),
    inference(resolution,[status(thm)],[c_40,c_135])).

tff(c_2627,plain,(
    ! [A_7,B_8] : k5_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2513])).

tff(c_2844,plain,(
    ! [A_162,B_163] : k5_xboole_0(k3_xboole_0(A_162,B_163),A_162) = k4_xboole_0(A_162,B_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_2627])).

tff(c_2916,plain,(
    ! [A_49,B_50] : k5_xboole_0(k1_tarski(A_49),k1_tarski(A_49)) = k4_xboole_0(k1_tarski(A_49),k2_tarski(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_2844])).

tff(c_2954,plain,(
    ! [A_164,B_165] : k4_xboole_0(k1_tarski(A_164),k2_tarski(A_164,B_165)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_2916])).

tff(c_2962,plain,(
    ! [A_164,B_165] : k2_xboole_0(k2_tarski(A_164,B_165),k1_tarski(A_164)) = k5_xboole_0(k2_tarski(A_164,B_165),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_24])).

tff(c_21219,plain,(
    ! [A_356,B_357] : k2_xboole_0(k2_tarski(A_356,B_357),k1_tarski(A_356)) = k2_tarski(A_356,B_357) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_4,c_2962])).

tff(c_21363,plain,(
    ! [A_356,B_357] : k2_xboole_0(k1_tarski(A_356),k2_tarski(A_356,B_357)) = k2_tarski(A_356,B_357) ),
    inference(superposition,[status(thm),theory(equality)],[c_6527,c_21219])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_21587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21363,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.45/3.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.99  
% 9.45/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.99  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 9.45/3.99  
% 9.45/3.99  %Foreground sorts:
% 9.45/3.99  
% 9.45/3.99  
% 9.45/3.99  %Background operators:
% 9.45/3.99  
% 9.45/3.99  
% 9.45/3.99  %Foreground operators:
% 9.45/3.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.45/3.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.45/3.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.45/3.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.45/3.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.45/3.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.45/3.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.45/3.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.45/3.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.45/3.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.45/3.99  tff('#skF_2', type, '#skF_2': $i).
% 9.45/3.99  tff('#skF_1', type, '#skF_1': $i).
% 9.45/3.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.45/3.99  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.45/3.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.45/3.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.45/3.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.45/3.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.45/3.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.45/3.99  
% 9.52/4.00  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.52/4.00  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.52/4.00  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.52/4.00  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.52/4.00  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.52/4.00  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.52/4.00  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.52/4.00  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.52/4.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.52/4.00  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.52/4.00  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 9.52/4.00  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 9.52/4.00  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.52/4.00  tff(c_321, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k4_xboole_0(B_79, A_78))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.52/4.00  tff(c_345, plain, (![A_80]: (k5_xboole_0(k1_xboole_0, A_80)=k2_xboole_0(k1_xboole_0, A_80))), inference(superposition, [status(thm), theory('equality')], [c_16, c_321])).
% 9.52/4.00  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.52/4.00  tff(c_362, plain, (![A_80]: (k5_xboole_0(A_80, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_80))), inference(superposition, [status(thm), theory('equality')], [c_345, c_4])).
% 9.52/4.00  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.52/4.00  tff(c_135, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/4.00  tff(c_147, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_135])).
% 9.52/4.00  tff(c_175, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.52/4.00  tff(c_190, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_175])).
% 9.52/4.00  tff(c_299, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.52/4.00  tff(c_311, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_147, c_299])).
% 9.52/4.00  tff(c_386, plain, (![B_81]: (k5_xboole_0(B_81, B_81)=k3_xboole_0(B_81, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_311])).
% 9.52/4.00  tff(c_342, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k2_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_321])).
% 9.52/4.00  tff(c_393, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_386, c_342])).
% 9.52/4.00  tff(c_402, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_147, c_393])).
% 9.52/4.00  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.52/4.00  tff(c_641, plain, (![B_93]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_93))=k4_xboole_0(k1_xboole_0, B_93))), inference(superposition, [status(thm), theory('equality')], [c_345, c_12])).
% 9.52/4.00  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.52/4.00  tff(c_146, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(resolution, [status(thm)], [c_20, c_135])).
% 9.52/4.00  tff(c_774, plain, (![B_106]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_106))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_641, c_146])).
% 9.52/4.00  tff(c_356, plain, (![B_8]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_8))=k4_xboole_0(k1_xboole_0, B_8))), inference(superposition, [status(thm), theory('equality')], [c_345, c_12])).
% 9.52/4.00  tff(c_781, plain, (![B_106]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_106))=k2_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_774, c_356])).
% 9.52/4.00  tff(c_851, plain, (![B_108]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_108))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_402, c_781])).
% 9.52/4.00  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.52/4.00  tff(c_919, plain, (![B_109]: (k3_xboole_0(k1_xboole_0, B_109)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_851, c_18])).
% 9.52/4.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.52/4.00  tff(c_314, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_299])).
% 9.52/4.00  tff(c_927, plain, (![B_109]: (k5_xboole_0(B_109, k1_xboole_0)=k4_xboole_0(B_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_919, c_314])).
% 9.52/4.00  tff(c_969, plain, (![B_109]: (k2_xboole_0(k1_xboole_0, B_109)=B_109)), inference(demodulation, [status(thm), theory('equality')], [c_362, c_16, c_927])).
% 9.52/4.00  tff(c_1114, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_969, c_342])).
% 9.52/4.00  tff(c_24, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.52/4.00  tff(c_477, plain, (![A_86, B_87, C_88]: (k5_xboole_0(k5_xboole_0(A_86, B_87), C_88)=k5_xboole_0(A_86, k5_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.52/4.00  tff(c_2036, plain, (![B_149, A_150, B_151]: (k5_xboole_0(B_149, k5_xboole_0(A_150, B_151))=k5_xboole_0(A_150, k5_xboole_0(B_151, B_149)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_477])).
% 9.52/4.00  tff(c_2513, plain, (![A_156, B_157]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_156, B_157))=k5_xboole_0(B_157, A_156))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_2036])).
% 9.52/4.00  tff(c_2624, plain, (![B_20, A_19]: (k5_xboole_0(k4_xboole_0(B_20, A_19), A_19)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2513])).
% 9.52/4.00  tff(c_2661, plain, (![B_20, A_19]: (k5_xboole_0(k4_xboole_0(B_20, A_19), A_19)=k2_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_2624])).
% 9.52/4.00  tff(c_2618, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_314, c_2513])).
% 9.52/4.00  tff(c_2660, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_2618])).
% 9.52/4.00  tff(c_6318, plain, (![A_230, B_231, C_232]: (k5_xboole_0(A_230, k5_xboole_0(k3_xboole_0(A_230, B_231), C_232))=k5_xboole_0(k4_xboole_0(A_230, B_231), C_232))), inference(superposition, [status(thm), theory('equality')], [c_12, c_477])).
% 9.52/4.00  tff(c_6410, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2660, c_6318])).
% 9.52/4.00  tff(c_6527, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_24, c_6410])).
% 9.52/4.00  tff(c_962, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_919])).
% 9.52/4.00  tff(c_320, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k3_xboole_0(B_6, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_311])).
% 9.52/4.00  tff(c_1046, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_962, c_320])).
% 9.52/4.00  tff(c_40, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), k2_tarski(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.52/4.00  tff(c_145, plain, (![A_49, B_50]: (k3_xboole_0(k1_tarski(A_49), k2_tarski(A_49, B_50))=k1_tarski(A_49))), inference(resolution, [status(thm)], [c_40, c_135])).
% 9.52/4.00  tff(c_2627, plain, (![A_7, B_8]: (k5_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2513])).
% 9.52/4.00  tff(c_2844, plain, (![A_162, B_163]: (k5_xboole_0(k3_xboole_0(A_162, B_163), A_162)=k4_xboole_0(A_162, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_2627])).
% 9.52/4.00  tff(c_2916, plain, (![A_49, B_50]: (k5_xboole_0(k1_tarski(A_49), k1_tarski(A_49))=k4_xboole_0(k1_tarski(A_49), k2_tarski(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_2844])).
% 9.52/4.00  tff(c_2954, plain, (![A_164, B_165]: (k4_xboole_0(k1_tarski(A_164), k2_tarski(A_164, B_165))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_2916])).
% 9.52/4.00  tff(c_2962, plain, (![A_164, B_165]: (k2_xboole_0(k2_tarski(A_164, B_165), k1_tarski(A_164))=k5_xboole_0(k2_tarski(A_164, B_165), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_24])).
% 9.52/4.00  tff(c_21219, plain, (![A_356, B_357]: (k2_xboole_0(k2_tarski(A_356, B_357), k1_tarski(A_356))=k2_tarski(A_356, B_357))), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_4, c_2962])).
% 9.52/4.00  tff(c_21363, plain, (![A_356, B_357]: (k2_xboole_0(k1_tarski(A_356), k2_tarski(A_356, B_357))=k2_tarski(A_356, B_357))), inference(superposition, [status(thm), theory('equality')], [c_6527, c_21219])).
% 9.52/4.00  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.52/4.00  tff(c_21587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21363, c_42])).
% 9.52/4.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.52/4.00  
% 9.52/4.00  Inference rules
% 9.52/4.00  ----------------------
% 9.52/4.00  #Ref     : 0
% 9.52/4.00  #Sup     : 5358
% 9.52/4.00  #Fact    : 0
% 9.52/4.00  #Define  : 0
% 9.52/4.00  #Split   : 0
% 9.52/4.00  #Chain   : 0
% 9.52/4.00  #Close   : 0
% 9.52/4.00  
% 9.52/4.00  Ordering : KBO
% 9.52/4.00  
% 9.52/4.00  Simplification rules
% 9.52/4.00  ----------------------
% 9.52/4.00  #Subsume      : 287
% 9.52/4.00  #Demod        : 6848
% 9.52/4.00  #Tautology    : 3349
% 9.52/4.00  #SimpNegUnit  : 0
% 9.52/4.00  #BackRed      : 12
% 9.52/4.00  
% 9.52/4.00  #Partial instantiations: 0
% 9.52/4.00  #Strategies tried      : 1
% 9.52/4.00  
% 9.52/4.00  Timing (in seconds)
% 9.52/4.00  ----------------------
% 9.52/4.01  Preprocessing        : 0.30
% 9.52/4.01  Parsing              : 0.16
% 9.52/4.01  CNF conversion       : 0.02
% 9.52/4.01  Main loop            : 2.92
% 9.52/4.01  Inferencing          : 0.58
% 9.52/4.01  Reduction            : 1.78
% 9.52/4.01  Demodulation         : 1.61
% 9.52/4.01  BG Simplification    : 0.08
% 9.52/4.01  Subsumption          : 0.36
% 9.52/4.01  Abstraction          : 0.13
% 9.52/4.01  MUC search           : 0.00
% 9.52/4.01  Cooper               : 0.00
% 9.52/4.01  Total                : 3.25
% 9.52/4.01  Index Insertion      : 0.00
% 9.52/4.01  Index Deletion       : 0.00
% 9.52/4.01  Index Matching       : 0.00
% 9.52/4.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
