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
% DateTime   : Thu Dec  3 09:44:23 EST 2020

% Result     : Theorem 11.75s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 262 expanded)
%              Number of leaves         :   20 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 257 expanded)
%              Number of equality atoms :   65 ( 246 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_57,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_20])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_216,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),C_35) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_266,plain,(
    ! [A_7,C_35] : k4_xboole_0(A_7,k2_xboole_0(k1_xboole_0,C_35)) = k4_xboole_0(A_7,C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_216])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_8,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_101,plain,(
    ! [A_27] : k4_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_27] : k4_xboole_0(A_27,k1_xboole_0) = k3_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_16])).

tff(c_121,plain,(
    ! [A_27] : k3_xboole_0(A_27,A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_106])).

tff(c_164,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(k3_xboole_0(A_30,B_31),C_32) = k3_xboole_0(A_30,k4_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_191,plain,(
    ! [A_27,C_32] : k3_xboole_0(A_27,k4_xboole_0(A_27,C_32)) = k4_xboole_0(A_27,C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_164])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_994,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,k4_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_1008,plain,(
    ! [A_57,B_58,C_10] : k4_xboole_0(k3_xboole_0(A_57,k4_xboole_0(A_57,B_58)),C_10) = k4_xboole_0(A_57,k2_xboole_0(k3_xboole_0(A_57,B_58),C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_14])).

tff(c_1071,plain,(
    ! [A_57,B_58,C_10] : k4_xboole_0(A_57,k2_xboole_0(k3_xboole_0(A_57,B_58),C_10)) = k3_xboole_0(A_57,k4_xboole_0(A_57,k2_xboole_0(B_58,C_10))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18,c_1008])).

tff(c_50462,plain,(
    ! [A_364,B_365,C_366] : k4_xboole_0(A_364,k2_xboole_0(k3_xboole_0(A_364,B_365),C_366)) = k4_xboole_0(A_364,k2_xboole_0(B_365,C_366)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_1071])).

tff(c_51056,plain,(
    ! [C_366] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_366)) = k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,C_366)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_50462])).

tff(c_51221,plain,(
    ! [C_367] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_367)) = k4_xboole_0('#skF_1',C_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_51056])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_226,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(B_34,k4_xboole_0(A_33,B_34))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_100])).

tff(c_273,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(B_34,A_33)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_226])).

tff(c_263,plain,(
    ! [A_33,B_34,B_12] : k4_xboole_0(A_33,k2_xboole_0(B_34,k4_xboole_0(k4_xboole_0(A_33,B_34),B_12))) = k3_xboole_0(k4_xboole_0(A_33,B_34),B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_216])).

tff(c_8912,plain,(
    ! [A_154,B_155,B_156] : k4_xboole_0(A_154,k2_xboole_0(B_155,k4_xboole_0(A_154,k2_xboole_0(B_155,B_156)))) = k3_xboole_0(k4_xboole_0(A_154,B_155),B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_263])).

tff(c_9193,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(B_34,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_33,B_34),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_8912])).

tff(c_9283,plain,(
    ! [A_33,B_34] : k3_xboole_0(k4_xboole_0(A_33,B_34),A_33) = k4_xboole_0(A_33,B_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9193])).

tff(c_3240,plain,(
    ! [C_96,A_97,B_98] : k2_xboole_0(C_96,k3_xboole_0(A_97,k4_xboole_0(B_98,C_96))) = k2_xboole_0(C_96,k3_xboole_0(A_97,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_10])).

tff(c_3430,plain,(
    ! [A_7,A_97] : k2_xboole_0(A_7,k3_xboole_0(A_97,k1_xboole_0)) = k2_xboole_0(A_7,k3_xboole_0(A_97,A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_3240])).

tff(c_3486,plain,(
    ! [A_7,A_97] : k2_xboole_0(A_7,k3_xboole_0(A_97,A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_3430])).

tff(c_9124,plain,(
    ! [A_154,A_7,A_97] : k4_xboole_0(A_154,k2_xboole_0(A_7,k4_xboole_0(A_154,A_7))) = k3_xboole_0(k4_xboole_0(A_154,A_7),k3_xboole_0(A_97,A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3486,c_8912])).

tff(c_9263,plain,(
    ! [A_154,A_7,A_97] : k3_xboole_0(k4_xboole_0(A_154,A_7),k3_xboole_0(A_97,A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_10,c_9124])).

tff(c_11227,plain,(
    ! [A_174,B_175,C_176] : k4_xboole_0(k3_xboole_0(A_174,B_175),k3_xboole_0(A_174,k4_xboole_0(B_175,C_176))) = k3_xboole_0(k3_xboole_0(A_174,B_175),C_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_16])).

tff(c_11338,plain,(
    ! [B_175,C_176,B_34] : k4_xboole_0(k3_xboole_0(k4_xboole_0(k4_xboole_0(B_175,C_176),B_34),B_175),k4_xboole_0(k4_xboole_0(B_175,C_176),B_34)) = k3_xboole_0(k3_xboole_0(k4_xboole_0(k4_xboole_0(B_175,C_176),B_34),B_175),C_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_9283,c_11227])).

tff(c_11590,plain,(
    ! [B_175,C_176,B_34] : k3_xboole_0(k4_xboole_0(B_175,k2_xboole_0(C_176,B_34)),C_176) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9283,c_9263,c_14,c_16,c_14,c_18,c_14,c_11338])).

tff(c_51592,plain,(
    ! [C_368] : k3_xboole_0(k4_xboole_0('#skF_1',C_368),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_51221,c_11590])).

tff(c_281,plain,(
    ! [A_33,B_34,B_12] : k4_xboole_0(A_33,k2_xboole_0(B_34,k4_xboole_0(A_33,k2_xboole_0(B_34,B_12)))) = k3_xboole_0(k4_xboole_0(A_33,B_34),B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_263])).

tff(c_9219,plain,(
    ! [A_154,A_5,B_6] : k4_xboole_0(A_154,k2_xboole_0(A_5,k4_xboole_0(A_154,k2_xboole_0(A_5,B_6)))) = k3_xboole_0(k4_xboole_0(A_154,A_5),k4_xboole_0(B_6,A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_8912])).

tff(c_9290,plain,(
    ! [A_154,A_5,B_6] : k3_xboole_0(k4_xboole_0(A_154,A_5),k4_xboole_0(B_6,A_5)) = k3_xboole_0(k4_xboole_0(A_154,A_5),B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_9219])).

tff(c_51629,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_51592,c_9290])).

tff(c_171,plain,(
    ! [A_30,B_31] : k3_xboole_0(A_30,k4_xboole_0(B_31,k3_xboole_0(A_30,B_31))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_100])).

tff(c_91,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_1295,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_91])).

tff(c_1338,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(B_31,k3_xboole_0(A_30,B_31))) = k4_xboole_0(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_1295])).

tff(c_11661,plain,(
    ! [A_177,B_178] : k4_xboole_0(A_177,k4_xboole_0(B_178,k3_xboole_0(A_177,B_178))) = A_177 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1338])).

tff(c_259,plain,(
    ! [A_11,B_12,C_35] : k4_xboole_0(A_11,k2_xboole_0(k4_xboole_0(A_11,B_12),C_35)) = k4_xboole_0(k3_xboole_0(A_11,B_12),C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_216])).

tff(c_2114,plain,(
    ! [A_77,B_78,C_79] : k4_xboole_0(A_77,k2_xboole_0(k4_xboole_0(A_77,B_78),C_79)) = k3_xboole_0(A_77,k4_xboole_0(B_78,C_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_259])).

tff(c_2138,plain,(
    ! [C_79,B_78] : k3_xboole_0(C_79,k4_xboole_0(B_78,C_79)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2114,c_273])).

tff(c_11712,plain,(
    ! [B_178,A_177] : k3_xboole_0(k4_xboole_0(B_178,k3_xboole_0(A_177,B_178)),A_177) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11661,c_2138])).

tff(c_52037,plain,(
    k3_xboole_0(k4_xboole_0('#skF_2',k1_xboole_0),k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_51629,c_11712])).

tff(c_52123,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_52037])).

tff(c_52125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_52123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.75/6.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.75/6.11  
% 11.75/6.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.75/6.11  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.75/6.11  
% 11.75/6.11  %Foreground sorts:
% 11.75/6.11  
% 11.75/6.11  
% 11.75/6.11  %Background operators:
% 11.75/6.11  
% 11.75/6.11  
% 11.75/6.11  %Foreground operators:
% 11.75/6.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.75/6.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.75/6.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.75/6.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.75/6.11  tff('#skF_2', type, '#skF_2': $i).
% 11.75/6.11  tff('#skF_3', type, '#skF_3': $i).
% 11.75/6.11  tff('#skF_1', type, '#skF_1': $i).
% 11.75/6.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.75/6.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.75/6.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.75/6.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.75/6.11  
% 11.86/6.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.86/6.13  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.86/6.13  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.86/6.13  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.86/6.13  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.86/6.13  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.86/6.13  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.86/6.13  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.86/6.13  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.86/6.13  tff(c_57, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.86/6.13  tff(c_20, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.86/6.13  tff(c_65, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_57, c_20])).
% 11.86/6.13  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.86/6.13  tff(c_216, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), C_35)=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.86/6.13  tff(c_266, plain, (![A_7, C_35]: (k4_xboole_0(A_7, k2_xboole_0(k1_xboole_0, C_35))=k4_xboole_0(A_7, C_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_216])).
% 11.86/6.13  tff(c_22, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.86/6.13  tff(c_48, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.86/6.13  tff(c_52, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_48])).
% 11.86/6.13  tff(c_8, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.86/6.13  tff(c_79, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.86/6.13  tff(c_97, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 11.86/6.13  tff(c_101, plain, (![A_27]: (k4_xboole_0(A_27, A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_97])).
% 11.86/6.13  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.86/6.13  tff(c_106, plain, (![A_27]: (k4_xboole_0(A_27, k1_xboole_0)=k3_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_101, c_16])).
% 11.86/6.13  tff(c_121, plain, (![A_27]: (k3_xboole_0(A_27, A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_106])).
% 11.86/6.13  tff(c_164, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k3_xboole_0(A_30, B_31), C_32)=k3_xboole_0(A_30, k4_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.86/6.13  tff(c_191, plain, (![A_27, C_32]: (k3_xboole_0(A_27, k4_xboole_0(A_27, C_32))=k4_xboole_0(A_27, C_32))), inference(superposition, [status(thm), theory('equality')], [c_121, c_164])).
% 11.86/6.13  tff(c_14, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.86/6.13  tff(c_18, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.86/6.13  tff(c_994, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k3_xboole_0(A_57, k4_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_79])).
% 11.86/6.13  tff(c_1008, plain, (![A_57, B_58, C_10]: (k4_xboole_0(k3_xboole_0(A_57, k4_xboole_0(A_57, B_58)), C_10)=k4_xboole_0(A_57, k2_xboole_0(k3_xboole_0(A_57, B_58), C_10)))), inference(superposition, [status(thm), theory('equality')], [c_994, c_14])).
% 11.86/6.13  tff(c_1071, plain, (![A_57, B_58, C_10]: (k4_xboole_0(A_57, k2_xboole_0(k3_xboole_0(A_57, B_58), C_10))=k3_xboole_0(A_57, k4_xboole_0(A_57, k2_xboole_0(B_58, C_10))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18, c_1008])).
% 11.86/6.13  tff(c_50462, plain, (![A_364, B_365, C_366]: (k4_xboole_0(A_364, k2_xboole_0(k3_xboole_0(A_364, B_365), C_366))=k4_xboole_0(A_364, k2_xboole_0(B_365, C_366)))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_1071])).
% 11.86/6.13  tff(c_51056, plain, (![C_366]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_366))=k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, C_366)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_50462])).
% 11.86/6.13  tff(c_51221, plain, (![C_367]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_367))=k4_xboole_0('#skF_1', C_367))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_51056])).
% 11.86/6.13  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.86/6.13  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.86/6.13  tff(c_100, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_97])).
% 11.86/6.13  tff(c_226, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k4_xboole_0(A_33, B_34)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_100])).
% 11.86/6.13  tff(c_273, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(B_34, A_33))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_226])).
% 11.86/6.13  tff(c_263, plain, (![A_33, B_34, B_12]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k4_xboole_0(k4_xboole_0(A_33, B_34), B_12)))=k3_xboole_0(k4_xboole_0(A_33, B_34), B_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_216])).
% 11.86/6.13  tff(c_8912, plain, (![A_154, B_155, B_156]: (k4_xboole_0(A_154, k2_xboole_0(B_155, k4_xboole_0(A_154, k2_xboole_0(B_155, B_156))))=k3_xboole_0(k4_xboole_0(A_154, B_155), B_156))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_263])).
% 11.86/6.13  tff(c_9193, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_33, B_34), A_33))), inference(superposition, [status(thm), theory('equality')], [c_273, c_8912])).
% 11.86/6.13  tff(c_9283, plain, (![A_33, B_34]: (k3_xboole_0(k4_xboole_0(A_33, B_34), A_33)=k4_xboole_0(A_33, B_34))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9193])).
% 11.86/6.13  tff(c_3240, plain, (![C_96, A_97, B_98]: (k2_xboole_0(C_96, k3_xboole_0(A_97, k4_xboole_0(B_98, C_96)))=k2_xboole_0(C_96, k3_xboole_0(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_10])).
% 11.86/6.13  tff(c_3430, plain, (![A_7, A_97]: (k2_xboole_0(A_7, k3_xboole_0(A_97, k1_xboole_0))=k2_xboole_0(A_7, k3_xboole_0(A_97, A_7)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_3240])).
% 11.86/6.13  tff(c_3486, plain, (![A_7, A_97]: (k2_xboole_0(A_7, k3_xboole_0(A_97, A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_3430])).
% 11.86/6.13  tff(c_9124, plain, (![A_154, A_7, A_97]: (k4_xboole_0(A_154, k2_xboole_0(A_7, k4_xboole_0(A_154, A_7)))=k3_xboole_0(k4_xboole_0(A_154, A_7), k3_xboole_0(A_97, A_7)))), inference(superposition, [status(thm), theory('equality')], [c_3486, c_8912])).
% 11.86/6.13  tff(c_9263, plain, (![A_154, A_7, A_97]: (k3_xboole_0(k4_xboole_0(A_154, A_7), k3_xboole_0(A_97, A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_10, c_9124])).
% 11.86/6.13  tff(c_11227, plain, (![A_174, B_175, C_176]: (k4_xboole_0(k3_xboole_0(A_174, B_175), k3_xboole_0(A_174, k4_xboole_0(B_175, C_176)))=k3_xboole_0(k3_xboole_0(A_174, B_175), C_176))), inference(superposition, [status(thm), theory('equality')], [c_164, c_16])).
% 11.86/6.13  tff(c_11338, plain, (![B_175, C_176, B_34]: (k4_xboole_0(k3_xboole_0(k4_xboole_0(k4_xboole_0(B_175, C_176), B_34), B_175), k4_xboole_0(k4_xboole_0(B_175, C_176), B_34))=k3_xboole_0(k3_xboole_0(k4_xboole_0(k4_xboole_0(B_175, C_176), B_34), B_175), C_176))), inference(superposition, [status(thm), theory('equality')], [c_9283, c_11227])).
% 11.86/6.13  tff(c_11590, plain, (![B_175, C_176, B_34]: (k3_xboole_0(k4_xboole_0(B_175, k2_xboole_0(C_176, B_34)), C_176)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9283, c_9263, c_14, c_16, c_14, c_18, c_14, c_11338])).
% 11.86/6.13  tff(c_51592, plain, (![C_368]: (k3_xboole_0(k4_xboole_0('#skF_1', C_368), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_51221, c_11590])).
% 11.86/6.13  tff(c_281, plain, (![A_33, B_34, B_12]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k4_xboole_0(A_33, k2_xboole_0(B_34, B_12))))=k3_xboole_0(k4_xboole_0(A_33, B_34), B_12))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_263])).
% 11.86/6.13  tff(c_9219, plain, (![A_154, A_5, B_6]: (k4_xboole_0(A_154, k2_xboole_0(A_5, k4_xboole_0(A_154, k2_xboole_0(A_5, B_6))))=k3_xboole_0(k4_xboole_0(A_154, A_5), k4_xboole_0(B_6, A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_8912])).
% 11.86/6.13  tff(c_9290, plain, (![A_154, A_5, B_6]: (k3_xboole_0(k4_xboole_0(A_154, A_5), k4_xboole_0(B_6, A_5))=k3_xboole_0(k4_xboole_0(A_154, A_5), B_6))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_9219])).
% 11.86/6.13  tff(c_51629, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_51592, c_9290])).
% 11.86/6.13  tff(c_171, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k4_xboole_0(B_31, k3_xboole_0(A_30, B_31)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_164, c_100])).
% 11.86/6.13  tff(c_91, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_79])).
% 11.86/6.13  tff(c_1295, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_91])).
% 11.86/6.13  tff(c_1338, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(B_31, k3_xboole_0(A_30, B_31)))=k4_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_1295])).
% 11.86/6.13  tff(c_11661, plain, (![A_177, B_178]: (k4_xboole_0(A_177, k4_xboole_0(B_178, k3_xboole_0(A_177, B_178)))=A_177)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1338])).
% 11.86/6.13  tff(c_259, plain, (![A_11, B_12, C_35]: (k4_xboole_0(A_11, k2_xboole_0(k4_xboole_0(A_11, B_12), C_35))=k4_xboole_0(k3_xboole_0(A_11, B_12), C_35))), inference(superposition, [status(thm), theory('equality')], [c_16, c_216])).
% 11.86/6.13  tff(c_2114, plain, (![A_77, B_78, C_79]: (k4_xboole_0(A_77, k2_xboole_0(k4_xboole_0(A_77, B_78), C_79))=k3_xboole_0(A_77, k4_xboole_0(B_78, C_79)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_259])).
% 11.86/6.13  tff(c_2138, plain, (![C_79, B_78]: (k3_xboole_0(C_79, k4_xboole_0(B_78, C_79))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2114, c_273])).
% 11.86/6.13  tff(c_11712, plain, (![B_178, A_177]: (k3_xboole_0(k4_xboole_0(B_178, k3_xboole_0(A_177, B_178)), A_177)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11661, c_2138])).
% 11.86/6.13  tff(c_52037, plain, (k3_xboole_0(k4_xboole_0('#skF_2', k1_xboole_0), k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_51629, c_11712])).
% 11.86/6.13  tff(c_52123, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_52037])).
% 11.86/6.13  tff(c_52125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_52123])).
% 11.86/6.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.86/6.13  
% 11.86/6.13  Inference rules
% 11.86/6.13  ----------------------
% 11.86/6.13  #Ref     : 0
% 11.86/6.13  #Sup     : 12850
% 11.86/6.13  #Fact    : 0
% 11.86/6.13  #Define  : 0
% 11.86/6.13  #Split   : 0
% 11.86/6.13  #Chain   : 0
% 11.86/6.13  #Close   : 0
% 11.86/6.13  
% 11.86/6.13  Ordering : KBO
% 11.86/6.13  
% 11.86/6.13  Simplification rules
% 11.86/6.13  ----------------------
% 11.86/6.13  #Subsume      : 0
% 11.86/6.13  #Demod        : 15673
% 11.86/6.13  #Tautology    : 9509
% 11.86/6.13  #SimpNegUnit  : 1
% 11.86/6.13  #BackRed      : 3
% 11.86/6.13  
% 11.86/6.13  #Partial instantiations: 0
% 11.86/6.13  #Strategies tried      : 1
% 11.86/6.13  
% 11.86/6.13  Timing (in seconds)
% 11.86/6.13  ----------------------
% 11.86/6.13  Preprocessing        : 0.24
% 11.86/6.13  Parsing              : 0.13
% 11.86/6.13  CNF conversion       : 0.01
% 11.86/6.13  Main loop            : 5.16
% 11.86/6.13  Inferencing          : 0.90
% 11.86/6.13  Reduction            : 3.02
% 11.86/6.13  Demodulation         : 2.74
% 11.86/6.13  BG Simplification    : 0.10
% 11.86/6.13  Subsumption          : 0.93
% 11.86/6.13  Abstraction          : 0.20
% 11.86/6.14  MUC search           : 0.00
% 11.86/6.14  Cooper               : 0.00
% 11.86/6.14  Total                : 5.44
% 11.86/6.14  Index Insertion      : 0.00
% 11.86/6.14  Index Deletion       : 0.00
% 11.86/6.14  Index Matching       : 0.00
% 11.86/6.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
