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
% DateTime   : Thu Dec  3 09:44:54 EST 2020

% Result     : Theorem 9.38s
% Output     : CNFRefutation 9.38s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 263 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :   77 ( 257 expanded)
%              Number of equality atoms :   76 ( 256 expanded)
%              Maximal formula depth    :    5 (   3 average)
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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_214,plain,(
    ! [A_41,B_42] : k4_xboole_0(k2_xboole_0(A_41,B_42),B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = k2_xboole_0(A_41,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_6])).

tff(c_256,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_521,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_12])).

tff(c_529,plain,(
    ! [A_51] : k4_xboole_0(A_51,k1_xboole_0) = k3_xboole_0(A_51,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_16])).

tff(c_548,plain,(
    ! [A_51] : k3_xboole_0(A_51,A_51) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_529])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_268,plain,(
    ! [A_43] : k2_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_2])).

tff(c_152,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k4_xboole_0(B_39,A_38)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_170,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = k2_xboole_0(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_152])).

tff(c_290,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_170])).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_480,plain,(
    ! [A_49,B_50] : k5_xboole_0(k5_xboole_0(A_49,B_50),k2_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_513,plain,(
    ! [A_20] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,A_20)) = k3_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_480])).

tff(c_520,plain,(
    ! [A_20] : k3_xboole_0(A_20,A_20) = k2_xboole_0(A_20,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_513])).

tff(c_878,plain,(
    ! [A_20] : k2_xboole_0(A_20,A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_520])).

tff(c_251,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_50,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_30,B_29] : k4_xboole_0(A_30,k2_xboole_0(B_29,A_30)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_382,plain,(
    ! [A_47] : k4_xboole_0(k1_xboole_0,A_47) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_65])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_394,plain,(
    ! [A_47] : k5_xboole_0(A_47,k1_xboole_0) = k2_xboole_0(A_47,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_24])).

tff(c_437,plain,(
    ! [A_47] : k5_xboole_0(A_47,k1_xboole_0) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_394])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(k2_xboole_0(A_6,B_7),B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_220,plain,(
    ! [B_42,A_41] : k5_xboole_0(B_42,k4_xboole_0(A_41,B_42)) = k2_xboole_0(B_42,k2_xboole_0(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_24])).

tff(c_1737,plain,(
    ! [B_85,A_86] : k2_xboole_0(B_85,k2_xboole_0(A_86,B_85)) = k2_xboole_0(B_85,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_220])).

tff(c_1765,plain,(
    ! [A_86,B_85] : k4_xboole_0(k2_xboole_0(A_86,B_85),k2_xboole_0(B_85,A_86)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1737,c_65])).

tff(c_695,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k4_xboole_0(A_58,B_59),C_60) = k4_xboole_0(A_58,k2_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7182,plain,(
    ! [C_174,A_175,B_176] : k5_xboole_0(C_174,k4_xboole_0(A_175,k2_xboole_0(B_176,C_174))) = k2_xboole_0(C_174,k4_xboole_0(A_175,B_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_24])).

tff(c_7271,plain,(
    ! [A_86,B_85] : k2_xboole_0(A_86,k4_xboole_0(k2_xboole_0(A_86,B_85),B_85)) = k5_xboole_0(A_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1765,c_7182])).

tff(c_7356,plain,(
    ! [A_177,B_178] : k2_xboole_0(A_177,k4_xboole_0(A_177,B_178)) = A_177 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_8,c_7271])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | k4_xboole_0(B_4,A_3) != k4_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | k4_xboole_0(B_42,k2_xboole_0(A_41,B_42)) != k4_xboole_0(A_41,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_4])).

tff(c_1574,plain,(
    ! [A_79,B_80] :
      ( k2_xboole_0(A_79,B_80) = B_80
      | k4_xboole_0(A_79,B_80) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_226])).

tff(c_2509,plain,(
    ! [A_104,B_105] : k2_xboole_0(A_104,k2_xboole_0(B_105,A_104)) = k2_xboole_0(B_105,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1574])).

tff(c_2616,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2509])).

tff(c_7456,plain,(
    ! [A_177,B_178] : k2_xboole_0(k4_xboole_0(A_177,B_178),A_177) = k2_xboole_0(A_177,A_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_7356,c_2616])).

tff(c_8076,plain,(
    ! [A_183,B_184] : k2_xboole_0(k4_xboole_0(A_183,B_184),A_183) = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_7456])).

tff(c_565,plain,(
    ! [A_53,B_54,C_55] : k5_xboole_0(k5_xboole_0(A_53,B_54),C_55) = k5_xboole_0(A_53,k5_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1047,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k5_xboole_0(B_70,k5_xboole_0(A_69,B_70))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_565])).

tff(c_611,plain,(
    ! [A_20,C_55] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_55)) = k5_xboole_0(k1_xboole_0,C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_565])).

tff(c_621,plain,(
    ! [A_20,C_55] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_55)) = C_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_611])).

tff(c_1055,plain,(
    ! [B_70,A_69] : k5_xboole_0(B_70,k5_xboole_0(A_69,B_70)) = k5_xboole_0(A_69,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_621])).

tff(c_1149,plain,(
    ! [B_71,A_72] : k5_xboole_0(B_71,k5_xboole_0(A_72,B_71)) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_1055])).

tff(c_1158,plain,(
    ! [B_71,A_72] : k5_xboole_0(B_71,A_72) = k5_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_621])).

tff(c_1790,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1737])).

tff(c_337,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_368,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_337])).

tff(c_379,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_368])).

tff(c_981,plain,(
    ! [A_67,C_68] : k5_xboole_0(A_67,k5_xboole_0(A_67,C_68)) = C_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_611])).

tff(c_4047,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k2_xboole_0(A_131,B_132)) = k4_xboole_0(B_132,A_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_981])).

tff(c_510,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),k2_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_480])).

tff(c_4057,plain,(
    ! [B_132,A_131] : k5_xboole_0(k4_xboole_0(B_132,A_131),k2_xboole_0(k2_xboole_0(A_131,B_132),A_131)) = k3_xboole_0(A_131,k2_xboole_0(A_131,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_510])).

tff(c_4127,plain,(
    ! [A_131,B_132] : k5_xboole_0(k2_xboole_0(A_131,B_132),k4_xboole_0(B_132,A_131)) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_1790,c_379,c_2,c_4057])).

tff(c_8109,plain,(
    ! [A_183,B_184] : k5_xboole_0(A_183,k4_xboole_0(A_183,k4_xboole_0(A_183,B_184))) = k4_xboole_0(A_183,B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_8076,c_4127])).

tff(c_8314,plain,(
    ! [A_183,B_184] : k5_xboole_0(A_183,k3_xboole_0(A_183,B_184)) = k4_xboole_0(A_183,B_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8109])).

tff(c_26,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8314,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.38/3.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.38/3.73  
% 9.38/3.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.38/3.73  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 9.38/3.73  
% 9.38/3.73  %Foreground sorts:
% 9.38/3.73  
% 9.38/3.73  
% 9.38/3.73  %Background operators:
% 9.38/3.73  
% 9.38/3.73  
% 9.38/3.73  %Foreground operators:
% 9.38/3.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.38/3.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.38/3.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.38/3.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.38/3.73  tff('#skF_2', type, '#skF_2': $i).
% 9.38/3.73  tff('#skF_1', type, '#skF_1': $i).
% 9.38/3.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.38/3.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.38/3.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.38/3.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.38/3.73  
% 9.38/3.75  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.38/3.75  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.38/3.75  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 9.38/3.75  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 9.38/3.75  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.38/3.75  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.38/3.75  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.38/3.75  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.38/3.75  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.38/3.75  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 9.38/3.75  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.38/3.75  tff(f_54, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.38/3.75  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.38/3.75  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.38/3.75  tff(c_214, plain, (![A_41, B_42]: (k4_xboole_0(k2_xboole_0(A_41, B_42), B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.38/3.75  tff(c_230, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=k2_xboole_0(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_214, c_6])).
% 9.38/3.75  tff(c_256, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_230])).
% 9.38/3.75  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.38/3.75  tff(c_521, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_12])).
% 9.38/3.75  tff(c_529, plain, (![A_51]: (k4_xboole_0(A_51, k1_xboole_0)=k3_xboole_0(A_51, A_51))), inference(superposition, [status(thm), theory('equality')], [c_521, c_16])).
% 9.38/3.75  tff(c_548, plain, (![A_51]: (k3_xboole_0(A_51, A_51)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_529])).
% 9.38/3.75  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.38/3.75  tff(c_268, plain, (![A_43]: (k2_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_256, c_2])).
% 9.38/3.75  tff(c_152, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k4_xboole_0(B_39, A_38))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.38/3.75  tff(c_170, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=k2_xboole_0(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_152])).
% 9.38/3.75  tff(c_290, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_268, c_170])).
% 9.38/3.75  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.38/3.75  tff(c_480, plain, (![A_49, B_50]: (k5_xboole_0(k5_xboole_0(A_49, B_50), k2_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.38/3.75  tff(c_513, plain, (![A_20]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, A_20))=k3_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_480])).
% 9.38/3.75  tff(c_520, plain, (![A_20]: (k3_xboole_0(A_20, A_20)=k2_xboole_0(A_20, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_513])).
% 9.38/3.75  tff(c_878, plain, (![A_20]: (k2_xboole_0(A_20, A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_548, c_520])).
% 9.38/3.75  tff(c_251, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_230])).
% 9.38/3.75  tff(c_50, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.38/3.75  tff(c_65, plain, (![A_30, B_29]: (k4_xboole_0(A_30, k2_xboole_0(B_29, A_30))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_12])).
% 9.38/3.75  tff(c_382, plain, (![A_47]: (k4_xboole_0(k1_xboole_0, A_47)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_65])).
% 9.38/3.75  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.38/3.75  tff(c_394, plain, (![A_47]: (k5_xboole_0(A_47, k1_xboole_0)=k2_xboole_0(A_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_382, c_24])).
% 9.38/3.75  tff(c_437, plain, (![A_47]: (k5_xboole_0(A_47, k1_xboole_0)=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_251, c_394])).
% 9.38/3.75  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.38/3.75  tff(c_220, plain, (![B_42, A_41]: (k5_xboole_0(B_42, k4_xboole_0(A_41, B_42))=k2_xboole_0(B_42, k2_xboole_0(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_214, c_24])).
% 9.38/3.75  tff(c_1737, plain, (![B_85, A_86]: (k2_xboole_0(B_85, k2_xboole_0(A_86, B_85))=k2_xboole_0(B_85, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_220])).
% 9.38/3.75  tff(c_1765, plain, (![A_86, B_85]: (k4_xboole_0(k2_xboole_0(A_86, B_85), k2_xboole_0(B_85, A_86))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1737, c_65])).
% 9.38/3.75  tff(c_695, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k4_xboole_0(A_58, B_59), C_60)=k4_xboole_0(A_58, k2_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.38/3.75  tff(c_7182, plain, (![C_174, A_175, B_176]: (k5_xboole_0(C_174, k4_xboole_0(A_175, k2_xboole_0(B_176, C_174)))=k2_xboole_0(C_174, k4_xboole_0(A_175, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_695, c_24])).
% 9.38/3.75  tff(c_7271, plain, (![A_86, B_85]: (k2_xboole_0(A_86, k4_xboole_0(k2_xboole_0(A_86, B_85), B_85))=k5_xboole_0(A_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1765, c_7182])).
% 9.38/3.75  tff(c_7356, plain, (![A_177, B_178]: (k2_xboole_0(A_177, k4_xboole_0(A_177, B_178))=A_177)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_8, c_7271])).
% 9.38/3.75  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | k4_xboole_0(B_4, A_3)!=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.38/3.75  tff(c_226, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | k4_xboole_0(B_42, k2_xboole_0(A_41, B_42))!=k4_xboole_0(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_214, c_4])).
% 9.38/3.75  tff(c_1574, plain, (![A_79, B_80]: (k2_xboole_0(A_79, B_80)=B_80 | k4_xboole_0(A_79, B_80)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_226])).
% 9.38/3.75  tff(c_2509, plain, (![A_104, B_105]: (k2_xboole_0(A_104, k2_xboole_0(B_105, A_104))=k2_xboole_0(B_105, A_104))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1574])).
% 9.38/3.75  tff(c_2616, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2509])).
% 9.38/3.75  tff(c_7456, plain, (![A_177, B_178]: (k2_xboole_0(k4_xboole_0(A_177, B_178), A_177)=k2_xboole_0(A_177, A_177))), inference(superposition, [status(thm), theory('equality')], [c_7356, c_2616])).
% 9.38/3.75  tff(c_8076, plain, (![A_183, B_184]: (k2_xboole_0(k4_xboole_0(A_183, B_184), A_183)=A_183)), inference(demodulation, [status(thm), theory('equality')], [c_878, c_7456])).
% 9.38/3.75  tff(c_565, plain, (![A_53, B_54, C_55]: (k5_xboole_0(k5_xboole_0(A_53, B_54), C_55)=k5_xboole_0(A_53, k5_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.38/3.75  tff(c_1047, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k5_xboole_0(B_70, k5_xboole_0(A_69, B_70)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_565])).
% 9.38/3.75  tff(c_611, plain, (![A_20, C_55]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_55))=k5_xboole_0(k1_xboole_0, C_55))), inference(superposition, [status(thm), theory('equality')], [c_20, c_565])).
% 9.38/3.75  tff(c_621, plain, (![A_20, C_55]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_55))=C_55)), inference(demodulation, [status(thm), theory('equality')], [c_290, c_611])).
% 9.38/3.75  tff(c_1055, plain, (![B_70, A_69]: (k5_xboole_0(B_70, k5_xboole_0(A_69, B_70))=k5_xboole_0(A_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1047, c_621])).
% 9.38/3.75  tff(c_1149, plain, (![B_71, A_72]: (k5_xboole_0(B_71, k5_xboole_0(A_72, B_71))=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_1055])).
% 9.38/3.75  tff(c_1158, plain, (![B_71, A_72]: (k5_xboole_0(B_71, A_72)=k5_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_1149, c_621])).
% 9.38/3.75  tff(c_1790, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1737])).
% 9.38/3.75  tff(c_337, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.38/3.75  tff(c_368, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_337])).
% 9.38/3.75  tff(c_379, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_368])).
% 9.38/3.75  tff(c_981, plain, (![A_67, C_68]: (k5_xboole_0(A_67, k5_xboole_0(A_67, C_68))=C_68)), inference(demodulation, [status(thm), theory('equality')], [c_290, c_611])).
% 9.38/3.75  tff(c_4047, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k2_xboole_0(A_131, B_132))=k4_xboole_0(B_132, A_131))), inference(superposition, [status(thm), theory('equality')], [c_24, c_981])).
% 9.38/3.75  tff(c_510, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), k2_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_480])).
% 9.38/3.75  tff(c_4057, plain, (![B_132, A_131]: (k5_xboole_0(k4_xboole_0(B_132, A_131), k2_xboole_0(k2_xboole_0(A_131, B_132), A_131))=k3_xboole_0(A_131, k2_xboole_0(A_131, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_4047, c_510])).
% 9.38/3.75  tff(c_4127, plain, (![A_131, B_132]: (k5_xboole_0(k2_xboole_0(A_131, B_132), k4_xboole_0(B_132, A_131))=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_1158, c_1790, c_379, c_2, c_4057])).
% 9.38/3.75  tff(c_8109, plain, (![A_183, B_184]: (k5_xboole_0(A_183, k4_xboole_0(A_183, k4_xboole_0(A_183, B_184)))=k4_xboole_0(A_183, B_184))), inference(superposition, [status(thm), theory('equality')], [c_8076, c_4127])).
% 9.38/3.75  tff(c_8314, plain, (![A_183, B_184]: (k5_xboole_0(A_183, k3_xboole_0(A_183, B_184))=k4_xboole_0(A_183, B_184))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8109])).
% 9.38/3.75  tff(c_26, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.38/3.75  tff(c_22485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8314, c_26])).
% 9.38/3.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.38/3.75  
% 9.38/3.75  Inference rules
% 9.38/3.75  ----------------------
% 9.38/3.75  #Ref     : 2
% 9.38/3.75  #Sup     : 5690
% 9.38/3.75  #Fact    : 0
% 9.38/3.75  #Define  : 0
% 9.38/3.75  #Split   : 2
% 9.38/3.75  #Chain   : 0
% 9.38/3.75  #Close   : 0
% 9.38/3.75  
% 9.38/3.75  Ordering : KBO
% 9.38/3.75  
% 9.38/3.75  Simplification rules
% 9.38/3.75  ----------------------
% 9.38/3.75  #Subsume      : 347
% 9.38/3.75  #Demod        : 5472
% 9.38/3.75  #Tautology    : 3249
% 9.38/3.75  #SimpNegUnit  : 0
% 9.38/3.75  #BackRed      : 6
% 9.38/3.75  
% 9.38/3.75  #Partial instantiations: 0
% 9.38/3.75  #Strategies tried      : 1
% 9.38/3.75  
% 9.38/3.75  Timing (in seconds)
% 9.38/3.75  ----------------------
% 9.38/3.75  Preprocessing        : 0.28
% 9.38/3.75  Parsing              : 0.16
% 9.38/3.75  CNF conversion       : 0.02
% 9.38/3.75  Main loop            : 2.69
% 9.38/3.75  Inferencing          : 0.61
% 9.38/3.75  Reduction            : 1.49
% 9.38/3.75  Demodulation         : 1.33
% 9.38/3.75  BG Simplification    : 0.08
% 9.38/3.75  Subsumption          : 0.38
% 9.38/3.75  Abstraction          : 0.13
% 9.38/3.75  MUC search           : 0.00
% 9.38/3.75  Cooper               : 0.00
% 9.38/3.75  Total                : 3.01
% 9.38/3.75  Index Insertion      : 0.00
% 9.38/3.75  Index Deletion       : 0.00
% 9.38/3.75  Index Matching       : 0.00
% 9.38/3.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
