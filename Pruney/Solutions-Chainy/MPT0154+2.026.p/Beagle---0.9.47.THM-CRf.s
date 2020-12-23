%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:07 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 735 expanded)
%              Number of leaves         :   27 ( 255 expanded)
%              Depth                    :   20
%              Number of atoms          :   68 ( 723 expanded)
%              Number of equality atoms :   62 ( 717 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_176,plain,(
    ! [B_44] : k3_xboole_0(k1_xboole_0,B_44) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_12])).

tff(c_206,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_278,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_287,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_278])).

tff(c_309,plain,(
    ! [A_50] : k4_xboole_0(A_50,k1_xboole_0) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_287])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_315,plain,(
    ! [A_50] : k4_xboole_0(A_50,A_50) = k3_xboole_0(A_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_10])).

tff(c_331,plain,(
    ! [A_50] : k4_xboole_0(A_50,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_315])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_302,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_278])).

tff(c_433,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_302])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_318,plain,(
    ! [A_50] : k5_xboole_0(k1_xboole_0,A_50) = k2_xboole_0(k1_xboole_0,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_20])).

tff(c_500,plain,(
    ! [A_60,B_61,C_62] : k5_xboole_0(k5_xboole_0(A_60,B_61),C_62) = k5_xboole_0(A_60,k5_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_534,plain,(
    ! [A_3,C_62] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_62)) = k5_xboole_0(k1_xboole_0,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_500])).

tff(c_1136,plain,(
    ! [A_90,C_91] : k5_xboole_0(A_90,k5_xboole_0(A_90,C_91)) = k2_xboole_0(k1_xboole_0,C_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_534])).

tff(c_1206,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_1136])).

tff(c_1233,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1206])).

tff(c_1240,plain,(
    ! [A_50] : k5_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_318])).

tff(c_24,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_22),k2_tarski(B_23,C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_218,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),k1_tarski(B_46)) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_424,plain,(
    ! [A_56,B_57] : r1_tarski(k1_tarski(A_56),k2_tarski(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_16])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_651,plain,(
    ! [A_70,B_71] : k3_xboole_0(k1_tarski(A_70),k2_tarski(A_70,B_71)) = k1_tarski(A_70) ),
    inference(resolution,[status(thm)],[c_424,c_8])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_660,plain,(
    ! [A_70,B_71] : k5_xboole_0(k1_tarski(A_70),k1_tarski(A_70)) = k4_xboole_0(k1_tarski(A_70),k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_6])).

tff(c_668,plain,(
    ! [A_70,B_71] : k4_xboole_0(k1_tarski(A_70),k2_tarski(A_70,B_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_660])).

tff(c_2244,plain,(
    ! [A_115,B_116,C_117] : k5_xboole_0(A_115,k5_xboole_0(k3_xboole_0(A_115,B_116),C_117)) = k5_xboole_0(k4_xboole_0(A_115,B_116),C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_500])).

tff(c_2339,plain,(
    ! [A_115,B_116] : k5_xboole_0(k4_xboole_0(A_115,B_116),k3_xboole_0(A_115,B_116)) = k5_xboole_0(A_115,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_2244])).

tff(c_2535,plain,(
    ! [A_122,B_123] : k5_xboole_0(k4_xboole_0(A_122,B_123),k3_xboole_0(A_122,B_123)) = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2339])).

tff(c_3888,plain,(
    ! [A_154,B_155] : k5_xboole_0(k4_xboole_0(A_154,B_155),k3_xboole_0(B_155,A_154)) = A_154 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2535])).

tff(c_566,plain,(
    ! [A_3,C_62] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_62)) = k2_xboole_0(k1_xboole_0,C_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_534])).

tff(c_1235,plain,(
    ! [A_3,C_62] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_62)) = C_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_566])).

tff(c_5126,plain,(
    ! [A_174,B_175] : k5_xboole_0(k4_xboole_0(A_174,B_175),A_174) = k3_xboole_0(B_175,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_3888,c_1235])).

tff(c_548,plain,(
    ! [A_18,B_19,C_62] : k5_xboole_0(A_18,k5_xboole_0(k4_xboole_0(B_19,A_18),C_62)) = k5_xboole_0(k2_xboole_0(A_18,B_19),C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_500])).

tff(c_5159,plain,(
    ! [B_175,A_174] : k5_xboole_0(k2_xboole_0(B_175,A_174),A_174) = k5_xboole_0(B_175,k3_xboole_0(B_175,A_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5126,c_548])).

tff(c_6801,plain,(
    ! [B_198,A_199] : k5_xboole_0(k2_xboole_0(B_198,A_199),A_199) = k4_xboole_0(B_198,A_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5159])).

tff(c_538,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k5_xboole_0(B_61,k5_xboole_0(A_60,B_61))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_500])).

tff(c_1600,plain,(
    ! [A_103,C_104] : k5_xboole_0(A_103,k5_xboole_0(A_103,C_104)) = C_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_566])).

tff(c_1654,plain,(
    ! [B_61,A_60] : k5_xboole_0(B_61,k5_xboole_0(A_60,B_61)) = k5_xboole_0(A_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_1600])).

tff(c_1700,plain,(
    ! [B_105,A_106] : k5_xboole_0(B_105,k5_xboole_0(A_106,B_105)) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1654])).

tff(c_1693,plain,(
    ! [B_61,A_60] : k5_xboole_0(B_61,k5_xboole_0(A_60,B_61)) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1654])).

tff(c_1703,plain,(
    ! [A_106,B_105] : k5_xboole_0(k5_xboole_0(A_106,B_105),A_106) = B_105 ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_1693])).

tff(c_11355,plain,(
    ! [B_252,A_253] : k5_xboole_0(k4_xboole_0(B_252,A_253),k2_xboole_0(B_252,A_253)) = A_253 ),
    inference(superposition,[status(thm),theory(equality)],[c_6801,c_1703])).

tff(c_11486,plain,(
    ! [A_70,B_71] : k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(A_70),k2_tarski(A_70,B_71))) = k2_tarski(A_70,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_11355])).

tff(c_11543,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_24,c_11486])).

tff(c_28,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_11552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11543,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.90/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.63  
% 6.90/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.63  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.90/2.63  
% 6.90/2.63  %Foreground sorts:
% 6.90/2.63  
% 6.90/2.63  
% 6.90/2.63  %Background operators:
% 6.90/2.63  
% 6.90/2.63  
% 6.90/2.63  %Foreground operators:
% 6.90/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.90/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.90/2.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.90/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.90/2.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.90/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.90/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.90/2.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.90/2.63  tff('#skF_2', type, '#skF_2': $i).
% 6.90/2.63  tff('#skF_1', type, '#skF_1': $i).
% 6.90/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.90/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.90/2.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.90/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.90/2.63  
% 7.10/2.64  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.10/2.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.10/2.64  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.10/2.64  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 7.10/2.64  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.10/2.64  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.10/2.64  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.10/2.64  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.10/2.64  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 7.10/2.64  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 7.10/2.64  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.10/2.64  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.10/2.64  tff(f_56, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.10/2.64  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.64  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.10/2.64  tff(c_146, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.10/2.64  tff(c_12, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.10/2.64  tff(c_176, plain, (![B_44]: (k3_xboole_0(k1_xboole_0, B_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_146, c_12])).
% 7.10/2.64  tff(c_206, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_176])).
% 7.10/2.64  tff(c_278, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.10/2.64  tff(c_287, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_206, c_278])).
% 7.10/2.64  tff(c_309, plain, (![A_50]: (k4_xboole_0(A_50, k1_xboole_0)=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_287])).
% 7.10/2.64  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.10/2.64  tff(c_315, plain, (![A_50]: (k4_xboole_0(A_50, A_50)=k3_xboole_0(A_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_309, c_10])).
% 7.10/2.64  tff(c_331, plain, (![A_50]: (k4_xboole_0(A_50, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_206, c_315])).
% 7.10/2.64  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.10/2.64  tff(c_302, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_278])).
% 7.10/2.64  tff(c_433, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_331, c_302])).
% 7.10/2.64  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.10/2.64  tff(c_318, plain, (![A_50]: (k5_xboole_0(k1_xboole_0, A_50)=k2_xboole_0(k1_xboole_0, A_50))), inference(superposition, [status(thm), theory('equality')], [c_309, c_20])).
% 7.10/2.64  tff(c_500, plain, (![A_60, B_61, C_62]: (k5_xboole_0(k5_xboole_0(A_60, B_61), C_62)=k5_xboole_0(A_60, k5_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.10/2.64  tff(c_534, plain, (![A_3, C_62]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_62))=k5_xboole_0(k1_xboole_0, C_62))), inference(superposition, [status(thm), theory('equality')], [c_433, c_500])).
% 7.10/2.64  tff(c_1136, plain, (![A_90, C_91]: (k5_xboole_0(A_90, k5_xboole_0(A_90, C_91))=k2_xboole_0(k1_xboole_0, C_91))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_534])).
% 7.10/2.64  tff(c_1206, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_433, c_1136])).
% 7.10/2.64  tff(c_1233, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1206])).
% 7.10/2.64  tff(c_1240, plain, (![A_50]: (k5_xboole_0(k1_xboole_0, A_50)=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_318])).
% 7.10/2.64  tff(c_24, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(B_23, C_24))=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.10/2.64  tff(c_218, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), k1_tarski(B_46))=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.10/2.64  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.10/2.64  tff(c_424, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), k2_tarski(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_218, c_16])).
% 7.10/2.64  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.10/2.64  tff(c_651, plain, (![A_70, B_71]: (k3_xboole_0(k1_tarski(A_70), k2_tarski(A_70, B_71))=k1_tarski(A_70))), inference(resolution, [status(thm)], [c_424, c_8])).
% 7.10/2.64  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.10/2.64  tff(c_660, plain, (![A_70, B_71]: (k5_xboole_0(k1_tarski(A_70), k1_tarski(A_70))=k4_xboole_0(k1_tarski(A_70), k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_651, c_6])).
% 7.10/2.64  tff(c_668, plain, (![A_70, B_71]: (k4_xboole_0(k1_tarski(A_70), k2_tarski(A_70, B_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_433, c_660])).
% 7.10/2.64  tff(c_2244, plain, (![A_115, B_116, C_117]: (k5_xboole_0(A_115, k5_xboole_0(k3_xboole_0(A_115, B_116), C_117))=k5_xboole_0(k4_xboole_0(A_115, B_116), C_117))), inference(superposition, [status(thm), theory('equality')], [c_6, c_500])).
% 7.10/2.64  tff(c_2339, plain, (![A_115, B_116]: (k5_xboole_0(k4_xboole_0(A_115, B_116), k3_xboole_0(A_115, B_116))=k5_xboole_0(A_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_433, c_2244])).
% 7.10/2.64  tff(c_2535, plain, (![A_122, B_123]: (k5_xboole_0(k4_xboole_0(A_122, B_123), k3_xboole_0(A_122, B_123))=A_122)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2339])).
% 7.10/2.64  tff(c_3888, plain, (![A_154, B_155]: (k5_xboole_0(k4_xboole_0(A_154, B_155), k3_xboole_0(B_155, A_154))=A_154)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2535])).
% 7.10/2.64  tff(c_566, plain, (![A_3, C_62]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_62))=k2_xboole_0(k1_xboole_0, C_62))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_534])).
% 7.10/2.64  tff(c_1235, plain, (![A_3, C_62]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_62))=C_62)), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_566])).
% 7.10/2.64  tff(c_5126, plain, (![A_174, B_175]: (k5_xboole_0(k4_xboole_0(A_174, B_175), A_174)=k3_xboole_0(B_175, A_174))), inference(superposition, [status(thm), theory('equality')], [c_3888, c_1235])).
% 7.10/2.64  tff(c_548, plain, (![A_18, B_19, C_62]: (k5_xboole_0(A_18, k5_xboole_0(k4_xboole_0(B_19, A_18), C_62))=k5_xboole_0(k2_xboole_0(A_18, B_19), C_62))), inference(superposition, [status(thm), theory('equality')], [c_20, c_500])).
% 7.10/2.64  tff(c_5159, plain, (![B_175, A_174]: (k5_xboole_0(k2_xboole_0(B_175, A_174), A_174)=k5_xboole_0(B_175, k3_xboole_0(B_175, A_174)))), inference(superposition, [status(thm), theory('equality')], [c_5126, c_548])).
% 7.10/2.64  tff(c_6801, plain, (![B_198, A_199]: (k5_xboole_0(k2_xboole_0(B_198, A_199), A_199)=k4_xboole_0(B_198, A_199))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5159])).
% 7.10/2.64  tff(c_538, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k5_xboole_0(B_61, k5_xboole_0(A_60, B_61)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_433, c_500])).
% 7.10/2.64  tff(c_1600, plain, (![A_103, C_104]: (k5_xboole_0(A_103, k5_xboole_0(A_103, C_104))=C_104)), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_566])).
% 7.10/2.64  tff(c_1654, plain, (![B_61, A_60]: (k5_xboole_0(B_61, k5_xboole_0(A_60, B_61))=k5_xboole_0(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_538, c_1600])).
% 7.10/2.64  tff(c_1700, plain, (![B_105, A_106]: (k5_xboole_0(B_105, k5_xboole_0(A_106, B_105))=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1654])).
% 7.10/2.64  tff(c_1693, plain, (![B_61, A_60]: (k5_xboole_0(B_61, k5_xboole_0(A_60, B_61))=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1654])).
% 7.10/2.64  tff(c_1703, plain, (![A_106, B_105]: (k5_xboole_0(k5_xboole_0(A_106, B_105), A_106)=B_105)), inference(superposition, [status(thm), theory('equality')], [c_1700, c_1693])).
% 7.10/2.64  tff(c_11355, plain, (![B_252, A_253]: (k5_xboole_0(k4_xboole_0(B_252, A_253), k2_xboole_0(B_252, A_253))=A_253)), inference(superposition, [status(thm), theory('equality')], [c_6801, c_1703])).
% 7.10/2.64  tff(c_11486, plain, (![A_70, B_71]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(k1_tarski(A_70), k2_tarski(A_70, B_71)))=k2_tarski(A_70, B_71))), inference(superposition, [status(thm), theory('equality')], [c_668, c_11355])).
% 7.10/2.64  tff(c_11543, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_24, c_11486])).
% 7.10/2.64  tff(c_28, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.10/2.64  tff(c_11552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11543, c_28])).
% 7.10/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.64  
% 7.10/2.64  Inference rules
% 7.10/2.64  ----------------------
% 7.10/2.64  #Ref     : 0
% 7.10/2.64  #Sup     : 2835
% 7.10/2.64  #Fact    : 0
% 7.10/2.64  #Define  : 0
% 7.10/2.64  #Split   : 0
% 7.10/2.64  #Chain   : 0
% 7.10/2.64  #Close   : 0
% 7.10/2.64  
% 7.10/2.64  Ordering : KBO
% 7.10/2.64  
% 7.10/2.64  Simplification rules
% 7.10/2.64  ----------------------
% 7.10/2.64  #Subsume      : 34
% 7.10/2.64  #Demod        : 3581
% 7.10/2.64  #Tautology    : 2044
% 7.10/2.64  #SimpNegUnit  : 0
% 7.10/2.64  #BackRed      : 9
% 7.10/2.64  
% 7.10/2.64  #Partial instantiations: 0
% 7.10/2.64  #Strategies tried      : 1
% 7.10/2.64  
% 7.10/2.64  Timing (in seconds)
% 7.10/2.64  ----------------------
% 7.10/2.65  Preprocessing        : 0.30
% 7.10/2.65  Parsing              : 0.17
% 7.10/2.65  CNF conversion       : 0.02
% 7.10/2.65  Main loop            : 1.52
% 7.10/2.65  Inferencing          : 0.43
% 7.10/2.65  Reduction            : 0.77
% 7.10/2.65  Demodulation         : 0.67
% 7.10/2.65  BG Simplification    : 0.05
% 7.10/2.65  Subsumption          : 0.19
% 7.10/2.65  Abstraction          : 0.08
% 7.10/2.65  MUC search           : 0.00
% 7.10/2.65  Cooper               : 0.00
% 7.10/2.65  Total                : 1.85
% 7.10/2.65  Index Insertion      : 0.00
% 7.10/2.65  Index Deletion       : 0.00
% 7.10/2.65  Index Matching       : 0.00
% 7.10/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
