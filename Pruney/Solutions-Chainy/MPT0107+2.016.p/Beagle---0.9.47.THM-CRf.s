%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:54 EST 2020

% Result     : Theorem 26.70s
% Output     : CNFRefutation 26.88s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 328 expanded)
%              Number of leaves         :   29 ( 120 expanded)
%              Depth                    :   19
%              Number of atoms          :   86 ( 325 expanded)
%              Number of equality atoms :   85 ( 324 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_198,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_214,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_24])).

tff(c_280,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_289,plain,(
    ! [A_46] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_280])).

tff(c_301,plain,(
    ! [A_46] : k4_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_289])).

tff(c_295,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_280])).

tff(c_1209,plain,(
    ! [A_90,B_91,C_92] : k4_xboole_0(k3_xboole_0(A_90,B_91),C_92) = k3_xboole_0(A_90,k4_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [A_29] : k5_xboole_0(A_29,k1_xboole_0) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_352,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k4_xboole_0(B_55,A_54)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_365,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = k2_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_352])).

tff(c_401,plain,(
    ! [A_57] : k2_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_365])).

tff(c_34,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_411,plain,(
    ! [A_57] : k4_xboole_0(A_57,A_57) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_34])).

tff(c_1239,plain,(
    ! [A_90,B_91] : k3_xboole_0(A_90,k4_xboole_0(B_91,k3_xboole_0(A_90,B_91))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_411])).

tff(c_1307,plain,(
    ! [A_90,B_91] : k3_xboole_0(A_90,k4_xboole_0(B_91,A_90)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_1239])).

tff(c_13165,plain,(
    ! [B_292,A_293,C_294] : k4_xboole_0(k3_xboole_0(B_292,A_293),C_294) = k3_xboole_0(A_293,k4_xboole_0(B_292,C_294)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1209])).

tff(c_13486,plain,(
    ! [B_91,A_90,C_294] : k3_xboole_0(k4_xboole_0(B_91,A_90),k4_xboole_0(A_90,C_294)) = k4_xboole_0(k1_xboole_0,C_294) ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_13165])).

tff(c_13576,plain,(
    ! [B_295,A_296,C_297] : k3_xboole_0(k4_xboole_0(B_295,A_296),k4_xboole_0(A_296,C_297)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_13486])).

tff(c_14223,plain,(
    ! [A_301,C_302,B_303] : k3_xboole_0(k4_xboole_0(A_301,C_302),k4_xboole_0(B_303,A_301)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13576])).

tff(c_36,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_574,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_577,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,k4_xboole_0(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_38])).

tff(c_622,plain,(
    ! [A_71,B_72] : k3_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_577])).

tff(c_14572,plain,(
    ! [A_304,C_305] : k4_xboole_0(k4_xboole_0(A_304,C_305),A_304) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14223,c_622])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k4_xboole_0(A_17,B_18),C_19) = k4_xboole_0(A_17,k2_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1866,plain,(
    ! [A_115,B_116] : k3_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_577])).

tff(c_1882,plain,(
    ! [A_115,B_116] : k4_xboole_0(k4_xboole_0(A_115,B_116),k4_xboole_0(A_115,B_116)) = k4_xboole_0(k4_xboole_0(A_115,B_116),A_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_295])).

tff(c_1937,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k2_xboole_0(B_116,A_115)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_411,c_1882])).

tff(c_48,plain,(
    ! [A_34,B_35] : k5_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_455,plain,(
    ! [A_59,B_60] : k4_xboole_0(k2_xboole_0(A_59,B_60),B_60) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_461,plain,(
    ! [B_60,A_59] : k5_xboole_0(B_60,k4_xboole_0(A_59,B_60)) = k2_xboole_0(B_60,k2_xboole_0(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_48])).

tff(c_2195,plain,(
    ! [B_126,A_127] : k2_xboole_0(B_126,k2_xboole_0(A_127,B_126)) = k2_xboole_0(B_126,A_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_461])).

tff(c_30,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2216,plain,(
    ! [B_126,A_127] : k4_xboole_0(k2_xboole_0(B_126,A_127),k2_xboole_0(A_127,B_126)) = k4_xboole_0(B_126,k2_xboole_0(A_127,B_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2195,c_30])).

tff(c_2249,plain,(
    ! [B_126,A_127] : k4_xboole_0(k2_xboole_0(B_126,A_127),k2_xboole_0(A_127,B_126)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_2216])).

tff(c_3456,plain,(
    ! [B_164,A_165] : k4_xboole_0(k2_xboole_0(B_164,A_165),k2_xboole_0(A_165,B_164)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_2216])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | k4_xboole_0(B_13,A_12) != k4_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3497,plain,(
    ! [B_164,A_165] :
      ( k2_xboole_0(B_164,A_165) = k2_xboole_0(A_165,B_164)
      | k4_xboole_0(k2_xboole_0(A_165,B_164),k2_xboole_0(B_164,A_165)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3456,c_26])).

tff(c_3573,plain,(
    ! [B_166,A_167] : k2_xboole_0(B_166,A_167) = k2_xboole_0(A_167,B_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2249,c_3497])).

tff(c_9984,plain,(
    ! [B_254,A_255] : k4_xboole_0(k2_xboole_0(B_254,A_255),B_254) = k4_xboole_0(A_255,B_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_3573,c_30])).

tff(c_10068,plain,(
    ! [B_254,A_255] :
      ( k2_xboole_0(B_254,A_255) = B_254
      | k4_xboole_0(B_254,k2_xboole_0(B_254,A_255)) != k4_xboole_0(A_255,B_254) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9984,c_26])).

tff(c_10153,plain,(
    ! [B_254,A_255] :
      ( k2_xboole_0(B_254,A_255) = B_254
      | k4_xboole_0(A_255,B_254) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10068])).

tff(c_14836,plain,(
    ! [A_304,C_305] : k2_xboole_0(A_304,k4_xboole_0(A_304,C_305)) = A_304 ),
    inference(superposition,[status(thm),theory(equality)],[c_14572,c_10153])).

tff(c_3559,plain,(
    ! [B_164,A_165] : k2_xboole_0(B_164,A_165) = k2_xboole_0(A_165,B_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2249,c_3497])).

tff(c_586,plain,(
    ! [A_71,B_72] : k5_xboole_0(k4_xboole_0(A_71,B_72),k3_xboole_0(A_71,B_72)) = k2_xboole_0(k4_xboole_0(A_71,B_72),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_48])).

tff(c_17706,plain,(
    ! [A_325,B_326] : k5_xboole_0(k4_xboole_0(A_325,B_326),k3_xboole_0(A_325,B_326)) = A_325 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14836,c_3559,c_586])).

tff(c_101,plain,(
    ! [B_42,A_43] : k5_xboole_0(B_42,A_43) = k5_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [A_43] : k5_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_42])).

tff(c_46,plain,(
    ! [A_33] : k5_xboole_0(A_33,A_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_890,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_954,plain,(
    ! [A_33,C_83] : k5_xboole_0(A_33,k5_xboole_0(A_33,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_890])).

tff(c_967,plain,(
    ! [A_33,C_83] : k5_xboole_0(A_33,k5_xboole_0(A_33,C_83)) = C_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_954])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_968,plain,(
    ! [A_84,C_85] : k5_xboole_0(A_84,k5_xboole_0(A_84,C_85)) = C_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_954])).

tff(c_1033,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k5_xboole_0(B_87,A_86)) = B_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_968])).

tff(c_1066,plain,(
    ! [A_33,C_83] : k5_xboole_0(k5_xboole_0(A_33,C_83),C_83) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_1033])).

tff(c_79422,plain,(
    ! [A_731,B_732] : k5_xboole_0(A_731,k3_xboole_0(A_731,B_732)) = k4_xboole_0(A_731,B_732) ),
    inference(superposition,[status(thm),theory(equality)],[c_17706,c_1066])).

tff(c_79715,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79422])).

tff(c_50,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_51,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_109293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79715,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.70/17.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.70/17.55  
% 26.70/17.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.80/17.55  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 26.80/17.55  
% 26.80/17.55  %Foreground sorts:
% 26.80/17.55  
% 26.80/17.55  
% 26.80/17.55  %Background operators:
% 26.80/17.55  
% 26.80/17.55  
% 26.80/17.55  %Foreground operators:
% 26.80/17.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 26.80/17.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.80/17.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.80/17.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.80/17.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.80/17.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 26.80/17.55  tff('#skF_3', type, '#skF_3': $i).
% 26.80/17.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.80/17.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.80/17.55  tff('#skF_4', type, '#skF_4': $i).
% 26.80/17.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.80/17.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.80/17.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.80/17.55  
% 26.88/17.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 26.88/17.57  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 26.88/17.57  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 26.88/17.57  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 26.88/17.57  tff(f_59, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 26.88/17.57  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 26.88/17.57  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 26.88/17.57  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 26.88/17.57  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 26.88/17.57  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 26.88/17.57  tff(f_49, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 26.88/17.57  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 26.88/17.57  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 26.88/17.57  tff(f_65, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 26.88/17.57  tff(f_63, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 26.88/17.57  tff(f_70, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 26.88/17.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 26.88/17.57  tff(c_28, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 26.88/17.57  tff(c_198, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 26.88/17.57  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.88/17.57  tff(c_214, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_198, c_24])).
% 26.88/17.57  tff(c_280, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 26.88/17.57  tff(c_289, plain, (![A_46]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_46))), inference(superposition, [status(thm), theory('equality')], [c_214, c_280])).
% 26.88/17.57  tff(c_301, plain, (![A_46]: (k4_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_289])).
% 26.88/17.57  tff(c_295, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_280])).
% 26.88/17.57  tff(c_1209, plain, (![A_90, B_91, C_92]: (k4_xboole_0(k3_xboole_0(A_90, B_91), C_92)=k3_xboole_0(A_90, k4_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 26.88/17.57  tff(c_42, plain, (![A_29]: (k5_xboole_0(A_29, k1_xboole_0)=A_29)), inference(cnfTransformation, [status(thm)], [f_61])).
% 26.88/17.57  tff(c_352, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k4_xboole_0(B_55, A_54))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_67])).
% 26.88/17.57  tff(c_365, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=k2_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_301, c_352])).
% 26.88/17.57  tff(c_401, plain, (![A_57]: (k2_xboole_0(A_57, k1_xboole_0)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_365])).
% 26.88/17.57  tff(c_34, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 26.88/17.57  tff(c_411, plain, (![A_57]: (k4_xboole_0(A_57, A_57)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_401, c_34])).
% 26.88/17.57  tff(c_1239, plain, (![A_90, B_91]: (k3_xboole_0(A_90, k4_xboole_0(B_91, k3_xboole_0(A_90, B_91)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1209, c_411])).
% 26.88/17.57  tff(c_1307, plain, (![A_90, B_91]: (k3_xboole_0(A_90, k4_xboole_0(B_91, A_90))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_295, c_1239])).
% 26.88/17.57  tff(c_13165, plain, (![B_292, A_293, C_294]: (k4_xboole_0(k3_xboole_0(B_292, A_293), C_294)=k3_xboole_0(A_293, k4_xboole_0(B_292, C_294)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1209])).
% 26.88/17.57  tff(c_13486, plain, (![B_91, A_90, C_294]: (k3_xboole_0(k4_xboole_0(B_91, A_90), k4_xboole_0(A_90, C_294))=k4_xboole_0(k1_xboole_0, C_294))), inference(superposition, [status(thm), theory('equality')], [c_1307, c_13165])).
% 26.88/17.57  tff(c_13576, plain, (![B_295, A_296, C_297]: (k3_xboole_0(k4_xboole_0(B_295, A_296), k4_xboole_0(A_296, C_297))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_13486])).
% 26.88/17.57  tff(c_14223, plain, (![A_301, C_302, B_303]: (k3_xboole_0(k4_xboole_0(A_301, C_302), k4_xboole_0(B_303, A_301))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_13576])).
% 26.88/17.57  tff(c_36, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 26.88/17.57  tff(c_574, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 26.88/17.57  tff(c_38, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 26.88/17.57  tff(c_577, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k3_xboole_0(A_71, k4_xboole_0(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_574, c_38])).
% 26.88/17.57  tff(c_622, plain, (![A_71, B_72]: (k3_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_577])).
% 26.88/17.57  tff(c_14572, plain, (![A_304, C_305]: (k4_xboole_0(k4_xboole_0(A_304, C_305), A_304)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14223, c_622])).
% 26.88/17.57  tff(c_32, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k4_xboole_0(A_17, B_18), C_19)=k4_xboole_0(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 26.88/17.57  tff(c_1866, plain, (![A_115, B_116]: (k3_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_577])).
% 26.88/17.57  tff(c_1882, plain, (![A_115, B_116]: (k4_xboole_0(k4_xboole_0(A_115, B_116), k4_xboole_0(A_115, B_116))=k4_xboole_0(k4_xboole_0(A_115, B_116), A_115))), inference(superposition, [status(thm), theory('equality')], [c_1866, c_295])).
% 26.88/17.57  tff(c_1937, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k2_xboole_0(B_116, A_115))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_411, c_1882])).
% 26.88/17.57  tff(c_48, plain, (![A_34, B_35]: (k5_xboole_0(A_34, k4_xboole_0(B_35, A_34))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 26.88/17.57  tff(c_455, plain, (![A_59, B_60]: (k4_xboole_0(k2_xboole_0(A_59, B_60), B_60)=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.88/17.57  tff(c_461, plain, (![B_60, A_59]: (k5_xboole_0(B_60, k4_xboole_0(A_59, B_60))=k2_xboole_0(B_60, k2_xboole_0(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_455, c_48])).
% 26.88/17.57  tff(c_2195, plain, (![B_126, A_127]: (k2_xboole_0(B_126, k2_xboole_0(A_127, B_126))=k2_xboole_0(B_126, A_127))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_461])).
% 26.88/17.57  tff(c_30, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.88/17.57  tff(c_2216, plain, (![B_126, A_127]: (k4_xboole_0(k2_xboole_0(B_126, A_127), k2_xboole_0(A_127, B_126))=k4_xboole_0(B_126, k2_xboole_0(A_127, B_126)))), inference(superposition, [status(thm), theory('equality')], [c_2195, c_30])).
% 26.88/17.57  tff(c_2249, plain, (![B_126, A_127]: (k4_xboole_0(k2_xboole_0(B_126, A_127), k2_xboole_0(A_127, B_126))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_2216])).
% 26.88/17.57  tff(c_3456, plain, (![B_164, A_165]: (k4_xboole_0(k2_xboole_0(B_164, A_165), k2_xboole_0(A_165, B_164))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_2216])).
% 26.88/17.57  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | k4_xboole_0(B_13, A_12)!=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 26.88/17.57  tff(c_3497, plain, (![B_164, A_165]: (k2_xboole_0(B_164, A_165)=k2_xboole_0(A_165, B_164) | k4_xboole_0(k2_xboole_0(A_165, B_164), k2_xboole_0(B_164, A_165))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3456, c_26])).
% 26.88/17.57  tff(c_3573, plain, (![B_166, A_167]: (k2_xboole_0(B_166, A_167)=k2_xboole_0(A_167, B_166))), inference(demodulation, [status(thm), theory('equality')], [c_2249, c_3497])).
% 26.88/17.57  tff(c_9984, plain, (![B_254, A_255]: (k4_xboole_0(k2_xboole_0(B_254, A_255), B_254)=k4_xboole_0(A_255, B_254))), inference(superposition, [status(thm), theory('equality')], [c_3573, c_30])).
% 26.88/17.57  tff(c_10068, plain, (![B_254, A_255]: (k2_xboole_0(B_254, A_255)=B_254 | k4_xboole_0(B_254, k2_xboole_0(B_254, A_255))!=k4_xboole_0(A_255, B_254))), inference(superposition, [status(thm), theory('equality')], [c_9984, c_26])).
% 26.88/17.57  tff(c_10153, plain, (![B_254, A_255]: (k2_xboole_0(B_254, A_255)=B_254 | k4_xboole_0(A_255, B_254)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10068])).
% 26.88/17.57  tff(c_14836, plain, (![A_304, C_305]: (k2_xboole_0(A_304, k4_xboole_0(A_304, C_305))=A_304)), inference(superposition, [status(thm), theory('equality')], [c_14572, c_10153])).
% 26.88/17.57  tff(c_3559, plain, (![B_164, A_165]: (k2_xboole_0(B_164, A_165)=k2_xboole_0(A_165, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_2249, c_3497])).
% 26.88/17.57  tff(c_586, plain, (![A_71, B_72]: (k5_xboole_0(k4_xboole_0(A_71, B_72), k3_xboole_0(A_71, B_72))=k2_xboole_0(k4_xboole_0(A_71, B_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_574, c_48])).
% 26.88/17.57  tff(c_17706, plain, (![A_325, B_326]: (k5_xboole_0(k4_xboole_0(A_325, B_326), k3_xboole_0(A_325, B_326))=A_325)), inference(demodulation, [status(thm), theory('equality')], [c_14836, c_3559, c_586])).
% 26.88/17.57  tff(c_101, plain, (![B_42, A_43]: (k5_xboole_0(B_42, A_43)=k5_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 26.88/17.57  tff(c_117, plain, (![A_43]: (k5_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_101, c_42])).
% 26.88/17.57  tff(c_46, plain, (![A_33]: (k5_xboole_0(A_33, A_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 26.88/17.57  tff(c_890, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 26.88/17.57  tff(c_954, plain, (![A_33, C_83]: (k5_xboole_0(A_33, k5_xboole_0(A_33, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_46, c_890])).
% 26.88/17.57  tff(c_967, plain, (![A_33, C_83]: (k5_xboole_0(A_33, k5_xboole_0(A_33, C_83))=C_83)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_954])).
% 26.88/17.57  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 26.88/17.57  tff(c_968, plain, (![A_84, C_85]: (k5_xboole_0(A_84, k5_xboole_0(A_84, C_85))=C_85)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_954])).
% 26.88/17.57  tff(c_1033, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k5_xboole_0(B_87, A_86))=B_87)), inference(superposition, [status(thm), theory('equality')], [c_4, c_968])).
% 26.88/17.57  tff(c_1066, plain, (![A_33, C_83]: (k5_xboole_0(k5_xboole_0(A_33, C_83), C_83)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_967, c_1033])).
% 26.88/17.57  tff(c_79422, plain, (![A_731, B_732]: (k5_xboole_0(A_731, k3_xboole_0(A_731, B_732))=k4_xboole_0(A_731, B_732))), inference(superposition, [status(thm), theory('equality')], [c_17706, c_1066])).
% 26.88/17.57  tff(c_79715, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_79422])).
% 26.88/17.57  tff(c_50, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 26.88/17.57  tff(c_51, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 26.88/17.57  tff(c_109293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79715, c_51])).
% 26.88/17.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.88/17.57  
% 26.88/17.57  Inference rules
% 26.88/17.57  ----------------------
% 26.88/17.57  #Ref     : 2
% 26.88/17.57  #Sup     : 28624
% 26.88/17.57  #Fact    : 0
% 26.88/17.57  #Define  : 0
% 26.88/17.57  #Split   : 4
% 26.88/17.57  #Chain   : 0
% 26.88/17.57  #Close   : 0
% 26.88/17.57  
% 26.88/17.57  Ordering : KBO
% 26.88/17.57  
% 26.88/17.57  Simplification rules
% 26.88/17.57  ----------------------
% 26.88/17.57  #Subsume      : 5132
% 26.88/17.57  #Demod        : 30392
% 26.88/17.57  #Tautology    : 12821
% 26.88/17.57  #SimpNegUnit  : 0
% 26.88/17.57  #BackRed      : 6
% 26.88/17.57  
% 26.88/17.57  #Partial instantiations: 0
% 26.88/17.57  #Strategies tried      : 1
% 26.88/17.57  
% 26.88/17.57  Timing (in seconds)
% 26.88/17.57  ----------------------
% 26.88/17.57  Preprocessing        : 0.45
% 26.88/17.57  Parsing              : 0.25
% 26.88/17.58  CNF conversion       : 0.03
% 26.88/17.58  Main loop            : 16.19
% 26.88/17.58  Inferencing          : 1.84
% 26.88/17.58  Reduction            : 10.27
% 26.88/17.58  Demodulation         : 9.46
% 26.88/17.58  BG Simplification    : 0.27
% 26.88/17.58  Subsumption          : 3.13
% 26.88/17.58  Abstraction          : 0.47
% 26.88/17.58  MUC search           : 0.00
% 26.88/17.58  Cooper               : 0.00
% 26.88/17.58  Total                : 16.68
% 26.88/17.58  Index Insertion      : 0.00
% 26.88/17.58  Index Deletion       : 0.00
% 26.88/17.58  Index Matching       : 0.00
% 26.88/17.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
