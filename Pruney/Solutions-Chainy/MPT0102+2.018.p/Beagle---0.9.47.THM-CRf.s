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
% DateTime   : Thu Dec  3 09:44:43 EST 2020

% Result     : Theorem 54.93s
% Output     : CNFRefutation 54.93s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 269 expanded)
%              Number of leaves         :   22 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :   65 ( 259 expanded)
%              Number of equality atoms :   64 ( 258 expanded)
%              Maximal formula depth    :    4 (   3 average)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_85,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_27] : k2_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_10])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_521,plain,(
    ! [A_43,B_44] : k2_xboole_0(k4_xboole_0(A_43,B_44),k4_xboole_0(B_44,A_43)) = k5_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_859,plain,(
    ! [A_52] : k2_xboole_0(k4_xboole_0(k1_xboole_0,A_52),A_52) = k5_xboole_0(k1_xboole_0,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_521])).

tff(c_894,plain,(
    ! [B_15] : k2_xboole_0(k3_xboole_0(k1_xboole_0,B_15),k4_xboole_0(k1_xboole_0,B_15)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_859])).

tff(c_992,plain,(
    ! [B_55] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_55)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_894])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_560,plain,(
    ! [A_10] : k2_xboole_0(A_10,k4_xboole_0(k1_xboole_0,A_10)) = k5_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_521])).

tff(c_570,plain,(
    ! [A_10] : k2_xboole_0(A_10,k4_xboole_0(k1_xboole_0,A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_560])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_868,plain,(
    ! [A_52] : k2_xboole_0(A_52,k4_xboole_0(k1_xboole_0,A_52)) = k5_xboole_0(k1_xboole_0,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_2])).

tff(c_913,plain,(
    ! [A_52] : k5_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_868])).

tff(c_1136,plain,(
    ! [B_58] : k4_xboole_0(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_913])).

tff(c_1168,plain,(
    ! [B_58] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_16])).

tff(c_1206,plain,(
    ! [B_58] : k3_xboole_0(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1168])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_383,plain,(
    ! [A_39,B_40] : k2_xboole_0(k5_xboole_0(A_39,B_40),k3_xboole_0(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_401,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(A_39,B_40),k5_xboole_0(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_383])).

tff(c_997,plain,(
    ! [B_55] : k4_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_913])).

tff(c_1221,plain,(
    ! [B_59] : k3_xboole_0(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1168])).

tff(c_1274,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1221])).

tff(c_132,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_147,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_132])).

tff(c_1413,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_147])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1430,plain,(
    ! [A_63,C_13] : k4_xboole_0(A_63,k2_xboole_0(A_63,C_13)) = k4_xboole_0(k1_xboole_0,C_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_14])).

tff(c_1656,plain,(
    ! [A_69,C_70] : k4_xboole_0(A_69,k2_xboole_0(A_69,C_70)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_1430])).

tff(c_1688,plain,(
    ! [A_39,B_40] : k4_xboole_0(k3_xboole_0(A_39,B_40),k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_1656])).

tff(c_215,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3850,plain,(
    ! [A_108,B_109] : k2_xboole_0(k3_xboole_0(A_108,k4_xboole_0(A_108,B_109)),k3_xboole_0(A_108,B_109)) = A_108 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_215])).

tff(c_3910,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_39,B_40),k1_xboole_0),k3_xboole_0(k3_xboole_0(A_39,B_40),k2_xboole_0(A_39,B_40))) = k3_xboole_0(A_39,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_3850])).

tff(c_4004,plain,(
    ! [A_39,B_40] : k3_xboole_0(k2_xboole_0(A_39,B_40),k3_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1206,c_4,c_4,c_3910])).

tff(c_606,plain,(
    ! [A_46,B_47] : k4_xboole_0(k2_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = k5_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_624,plain,(
    ! [A_46,B_47] : k4_xboole_0(k2_xboole_0(A_46,B_47),k5_xboole_0(A_46,B_47)) = k3_xboole_0(k2_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_16])).

tff(c_151707,plain,(
    ! [A_46,B_47] : k4_xboole_0(k2_xboole_0(A_46,B_47),k5_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4004,c_624])).

tff(c_1353,plain,(
    ! [B_61,A_62] : k2_xboole_0(k5_xboole_0(B_61,A_62),k3_xboole_0(A_62,B_61)) = k2_xboole_0(B_61,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_383])).

tff(c_1391,plain,(
    ! [A_62,B_61] : k2_xboole_0(k3_xboole_0(A_62,B_61),k5_xboole_0(B_61,A_62)) = k2_xboole_0(B_61,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1353])).

tff(c_1883,plain,(
    ! [B_75,A_76] : k4_xboole_0(B_75,k2_xboole_0(A_76,B_75)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1656])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1900,plain,(
    ! [A_76,B_75] : k2_xboole_0(k4_xboole_0(k2_xboole_0(A_76,B_75),B_75),k1_xboole_0) = k5_xboole_0(k2_xboole_0(A_76,B_75),B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_1883,c_6])).

tff(c_214273,plain,(
    ! [A_878,B_879] : k5_xboole_0(k2_xboole_0(A_878,B_879),B_879) = k4_xboole_0(k2_xboole_0(A_878,B_879),B_879) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1900])).

tff(c_214723,plain,(
    ! [A_62,B_61] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_62,B_61),k5_xboole_0(B_61,A_62)),k5_xboole_0(B_61,A_62)) = k5_xboole_0(k2_xboole_0(B_61,A_62),k5_xboole_0(B_61,A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1391,c_214273])).

tff(c_214934,plain,(
    ! [B_61,A_62] : k5_xboole_0(k2_xboole_0(B_61,A_62),k5_xboole_0(B_61,A_62)) = k3_xboole_0(B_61,A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151707,c_1391,c_214723])).

tff(c_2248,plain,(
    ! [A_83,B_84] : k4_xboole_0(k2_xboole_0(A_83,B_84),k3_xboole_0(B_84,A_83)) = k5_xboole_0(B_84,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_606])).

tff(c_669,plain,(
    ! [B_4,A_3] : k4_xboole_0(k2_xboole_0(B_4,A_3),k3_xboole_0(A_3,B_4)) = k5_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_606])).

tff(c_2257,plain,(
    ! [B_84,A_83] : k5_xboole_0(B_84,A_83) = k5_xboole_0(A_83,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_2248,c_669])).

tff(c_24,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2362,plain,(
    k5_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_24])).

tff(c_220934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214934,c_2362])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 16:40:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 54.93/46.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.93/46.28  
% 54.93/46.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.93/46.28  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 54.93/46.28  
% 54.93/46.28  %Foreground sorts:
% 54.93/46.28  
% 54.93/46.28  
% 54.93/46.28  %Background operators:
% 54.93/46.28  
% 54.93/46.28  
% 54.93/46.28  %Foreground operators:
% 54.93/46.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 54.93/46.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 54.93/46.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 54.93/46.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 54.93/46.28  tff('#skF_2', type, '#skF_2': $i).
% 54.93/46.28  tff('#skF_1', type, '#skF_1': $i).
% 54.93/46.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 54.93/46.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 54.93/46.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 54.93/46.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 54.93/46.28  
% 54.93/46.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 54.93/46.29  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 54.93/46.29  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 54.93/46.29  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 54.93/46.29  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 54.93/46.29  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 54.93/46.29  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 54.93/46.29  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 54.93/46.29  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 54.93/46.29  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 54.93/46.29  tff(f_33, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 54.93/46.29  tff(f_50, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 54.93/46.29  tff(c_85, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 54.93/46.29  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 54.93/46.29  tff(c_101, plain, (![A_27]: (k2_xboole_0(k1_xboole_0, A_27)=A_27)), inference(superposition, [status(thm), theory('equality')], [c_85, c_10])).
% 54.93/46.29  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 54.93/46.29  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_43])).
% 54.93/46.29  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 54.93/46.29  tff(c_521, plain, (![A_43, B_44]: (k2_xboole_0(k4_xboole_0(A_43, B_44), k4_xboole_0(B_44, A_43))=k5_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 54.93/46.29  tff(c_859, plain, (![A_52]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_52), A_52)=k5_xboole_0(k1_xboole_0, A_52))), inference(superposition, [status(thm), theory('equality')], [c_12, c_521])).
% 54.93/46.29  tff(c_894, plain, (![B_15]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, B_15), k4_xboole_0(k1_xboole_0, B_15))=k5_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_859])).
% 54.93/46.29  tff(c_992, plain, (![B_55]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_55))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_894])).
% 54.93/46.29  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_45])).
% 54.93/46.29  tff(c_560, plain, (![A_10]: (k2_xboole_0(A_10, k4_xboole_0(k1_xboole_0, A_10))=k5_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_521])).
% 54.93/46.29  tff(c_570, plain, (![A_10]: (k2_xboole_0(A_10, k4_xboole_0(k1_xboole_0, A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_560])).
% 54.93/46.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 54.93/46.29  tff(c_868, plain, (![A_52]: (k2_xboole_0(A_52, k4_xboole_0(k1_xboole_0, A_52))=k5_xboole_0(k1_xboole_0, A_52))), inference(superposition, [status(thm), theory('equality')], [c_859, c_2])).
% 54.93/46.29  tff(c_913, plain, (![A_52]: (k5_xboole_0(k1_xboole_0, A_52)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_570, c_868])).
% 54.93/46.29  tff(c_1136, plain, (![B_58]: (k4_xboole_0(k1_xboole_0, B_58)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_992, c_913])).
% 54.93/46.29  tff(c_1168, plain, (![B_58]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_58))), inference(superposition, [status(thm), theory('equality')], [c_1136, c_16])).
% 54.93/46.29  tff(c_1206, plain, (![B_58]: (k3_xboole_0(k1_xboole_0, B_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1168])).
% 54.93/46.29  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 54.93/46.29  tff(c_383, plain, (![A_39, B_40]: (k2_xboole_0(k5_xboole_0(A_39, B_40), k3_xboole_0(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 54.93/46.29  tff(c_401, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(A_39, B_40), k5_xboole_0(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_383])).
% 54.93/46.29  tff(c_997, plain, (![B_55]: (k4_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_992, c_913])).
% 54.93/46.29  tff(c_1221, plain, (![B_59]: (k3_xboole_0(k1_xboole_0, B_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1168])).
% 54.93/46.29  tff(c_1274, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1221])).
% 54.93/46.29  tff(c_132, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 54.93/46.29  tff(c_147, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_132])).
% 54.93/46.29  tff(c_1413, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_147])).
% 54.93/46.29  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 54.93/46.29  tff(c_1430, plain, (![A_63, C_13]: (k4_xboole_0(A_63, k2_xboole_0(A_63, C_13))=k4_xboole_0(k1_xboole_0, C_13))), inference(superposition, [status(thm), theory('equality')], [c_1413, c_14])).
% 54.93/46.29  tff(c_1656, plain, (![A_69, C_70]: (k4_xboole_0(A_69, k2_xboole_0(A_69, C_70))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_997, c_1430])).
% 54.93/46.29  tff(c_1688, plain, (![A_39, B_40]: (k4_xboole_0(k3_xboole_0(A_39, B_40), k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_401, c_1656])).
% 54.93/46.29  tff(c_215, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_43])).
% 54.93/46.29  tff(c_3850, plain, (![A_108, B_109]: (k2_xboole_0(k3_xboole_0(A_108, k4_xboole_0(A_108, B_109)), k3_xboole_0(A_108, B_109))=A_108)), inference(superposition, [status(thm), theory('equality')], [c_16, c_215])).
% 54.93/46.29  tff(c_3910, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_39, B_40), k1_xboole_0), k3_xboole_0(k3_xboole_0(A_39, B_40), k2_xboole_0(A_39, B_40)))=k3_xboole_0(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_1688, c_3850])).
% 54.93/46.29  tff(c_4004, plain, (![A_39, B_40]: (k3_xboole_0(k2_xboole_0(A_39, B_40), k3_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1206, c_4, c_4, c_3910])).
% 54.93/46.29  tff(c_606, plain, (![A_46, B_47]: (k4_xboole_0(k2_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=k5_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 54.93/46.29  tff(c_624, plain, (![A_46, B_47]: (k4_xboole_0(k2_xboole_0(A_46, B_47), k5_xboole_0(A_46, B_47))=k3_xboole_0(k2_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_606, c_16])).
% 54.93/46.29  tff(c_151707, plain, (![A_46, B_47]: (k4_xboole_0(k2_xboole_0(A_46, B_47), k5_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_4004, c_624])).
% 54.93/46.29  tff(c_1353, plain, (![B_61, A_62]: (k2_xboole_0(k5_xboole_0(B_61, A_62), k3_xboole_0(A_62, B_61))=k2_xboole_0(B_61, A_62))), inference(superposition, [status(thm), theory('equality')], [c_4, c_383])).
% 54.93/46.29  tff(c_1391, plain, (![A_62, B_61]: (k2_xboole_0(k3_xboole_0(A_62, B_61), k5_xboole_0(B_61, A_62))=k2_xboole_0(B_61, A_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1353])).
% 54.93/46.29  tff(c_1883, plain, (![B_75, A_76]: (k4_xboole_0(B_75, k2_xboole_0(A_76, B_75))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1656])).
% 54.93/46.29  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 54.93/46.29  tff(c_1900, plain, (![A_76, B_75]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(A_76, B_75), B_75), k1_xboole_0)=k5_xboole_0(k2_xboole_0(A_76, B_75), B_75))), inference(superposition, [status(thm), theory('equality')], [c_1883, c_6])).
% 54.93/46.29  tff(c_214273, plain, (![A_878, B_879]: (k5_xboole_0(k2_xboole_0(A_878, B_879), B_879)=k4_xboole_0(k2_xboole_0(A_878, B_879), B_879))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1900])).
% 54.93/46.29  tff(c_214723, plain, (![A_62, B_61]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_62, B_61), k5_xboole_0(B_61, A_62)), k5_xboole_0(B_61, A_62))=k5_xboole_0(k2_xboole_0(B_61, A_62), k5_xboole_0(B_61, A_62)))), inference(superposition, [status(thm), theory('equality')], [c_1391, c_214273])).
% 54.93/46.29  tff(c_214934, plain, (![B_61, A_62]: (k5_xboole_0(k2_xboole_0(B_61, A_62), k5_xboole_0(B_61, A_62))=k3_xboole_0(B_61, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_151707, c_1391, c_214723])).
% 54.93/46.29  tff(c_2248, plain, (![A_83, B_84]: (k4_xboole_0(k2_xboole_0(A_83, B_84), k3_xboole_0(B_84, A_83))=k5_xboole_0(B_84, A_83))), inference(superposition, [status(thm), theory('equality')], [c_2, c_606])).
% 54.93/46.29  tff(c_669, plain, (![B_4, A_3]: (k4_xboole_0(k2_xboole_0(B_4, A_3), k3_xboole_0(A_3, B_4))=k5_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_606])).
% 54.93/46.29  tff(c_2257, plain, (![B_84, A_83]: (k5_xboole_0(B_84, A_83)=k5_xboole_0(A_83, B_84))), inference(superposition, [status(thm), theory('equality')], [c_2248, c_669])).
% 54.93/46.29  tff(c_24, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 54.93/46.29  tff(c_2362, plain, (k5_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_24])).
% 54.93/46.29  tff(c_220934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214934, c_2362])).
% 54.93/46.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.93/46.29  
% 54.93/46.29  Inference rules
% 54.93/46.29  ----------------------
% 54.93/46.29  #Ref     : 0
% 54.93/46.29  #Sup     : 56688
% 54.93/46.29  #Fact    : 0
% 54.93/46.29  #Define  : 0
% 54.93/46.29  #Split   : 0
% 54.93/46.29  #Chain   : 0
% 54.93/46.29  #Close   : 0
% 54.93/46.29  
% 54.93/46.29  Ordering : KBO
% 54.93/46.29  
% 54.93/46.29  Simplification rules
% 54.93/46.29  ----------------------
% 54.93/46.29  #Subsume      : 690
% 54.93/46.29  #Demod        : 82898
% 54.93/46.29  #Tautology    : 30435
% 54.93/46.29  #SimpNegUnit  : 0
% 54.93/46.29  #BackRed      : 32
% 54.93/46.29  
% 54.93/46.29  #Partial instantiations: 0
% 54.93/46.29  #Strategies tried      : 1
% 54.93/46.29  
% 54.93/46.29  Timing (in seconds)
% 54.93/46.29  ----------------------
% 54.93/46.30  Preprocessing        : 0.28
% 54.93/46.30  Parsing              : 0.16
% 54.93/46.30  CNF conversion       : 0.01
% 54.93/46.30  Main loop            : 45.18
% 54.93/46.30  Inferencing          : 3.56
% 54.93/46.30  Reduction            : 32.42
% 54.93/46.30  Demodulation         : 30.93
% 54.93/46.30  BG Simplification    : 0.56
% 54.93/46.30  Subsumption          : 7.16
% 54.93/46.30  Abstraction          : 1.19
% 54.93/46.30  MUC search           : 0.00
% 54.93/46.30  Cooper               : 0.00
% 54.93/46.30  Total                : 45.49
% 54.93/46.30  Index Insertion      : 0.00
% 54.93/46.30  Index Deletion       : 0.00
% 54.93/46.30  Index Matching       : 0.00
% 54.93/46.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
