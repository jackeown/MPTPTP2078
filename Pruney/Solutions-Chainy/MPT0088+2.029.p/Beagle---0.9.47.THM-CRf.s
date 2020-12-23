%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:23 EST 2020

% Result     : Theorem 11.12s
% Output     : CNFRefutation 11.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 606 expanded)
%              Number of leaves         :   20 ( 217 expanded)
%              Depth                    :   22
%              Number of atoms          :   80 ( 613 expanded)
%              Number of equality atoms :   68 ( 577 expanded)
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

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_43,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k3_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_20])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_115,plain,(
    ! [A_31] : k4_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_16,B_17] : k3_xboole_0(k4_xboole_0(A_16,B_17),B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_123,plain,(
    ! [A_31] : k3_xboole_0(k1_xboole_0,A_31) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_65])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k4_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)) = k4_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_489,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k4_xboole_0(A_47,B_48),C_49) = k4_xboole_0(A_47,k2_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_547,plain,(
    ! [A_8,B_9,C_49] : k4_xboole_0(A_8,k2_xboole_0(k4_xboole_0(A_8,B_9),C_49)) = k4_xboole_0(k3_xboole_0(A_8,B_9),C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_489])).

tff(c_567,plain,(
    ! [A_8,B_9,C_49] : k4_xboole_0(A_8,k2_xboole_0(k4_xboole_0(A_8,B_9),C_49)) = k3_xboole_0(A_8,k4_xboole_0(B_9,C_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_547])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k4_xboole_0(A_5,B_6),C_7) = k4_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_551,plain,(
    ! [A_47,B_48,B_9] : k4_xboole_0(A_47,k2_xboole_0(B_48,k4_xboole_0(k4_xboole_0(A_47,B_48),B_9))) = k3_xboole_0(k4_xboole_0(A_47,B_48),B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_489])).

tff(c_5318,plain,(
    ! [A_137,B_138,B_139] : k4_xboole_0(A_137,k2_xboole_0(B_138,k4_xboole_0(A_137,k2_xboole_0(B_138,B_139)))) = k3_xboole_0(k4_xboole_0(A_137,B_138),B_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_551])).

tff(c_5434,plain,(
    ! [A_8,B_9,C_49] : k4_xboole_0(A_8,k2_xboole_0(k4_xboole_0(A_8,B_9),k3_xboole_0(A_8,k4_xboole_0(B_9,C_49)))) = k3_xboole_0(k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)),C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_5318])).

tff(c_26520,plain,(
    ! [A_326,B_327,C_328] : k3_xboole_0(k3_xboole_0(A_326,B_327),C_328) = k3_xboole_0(A_326,k3_xboole_0(B_327,C_328)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16,c_12,c_5434])).

tff(c_120,plain,(
    ! [A_31] : k4_xboole_0(A_31,k1_xboole_0) = k3_xboole_0(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_12])).

tff(c_138,plain,(
    ! [A_31] : k3_xboole_0(A_31,A_31) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_120])).

tff(c_166,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k3_xboole_0(A_34,B_35),C_36) = k3_xboole_0(A_34,k4_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2623,plain,(
    ! [A_96,C_97] : k3_xboole_0(A_96,k4_xboole_0(A_96,C_97)) = k4_xboole_0(A_96,C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_166])).

tff(c_99,plain,(
    ! [A_29,B_30] : k3_xboole_0(k3_xboole_0(A_29,B_30),k4_xboole_0(A_29,B_30)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_65])).

tff(c_2656,plain,(
    ! [A_96,C_97] : k3_xboole_0(k4_xboole_0(A_96,C_97),k4_xboole_0(A_96,k4_xboole_0(A_96,C_97))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_99])).

tff(c_2720,plain,(
    ! [A_96,C_97] : k3_xboole_0(k4_xboole_0(A_96,C_97),k3_xboole_0(A_96,C_97)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2656])).

tff(c_180,plain,(
    ! [A_34,B_35,B_9] : k3_xboole_0(A_34,k4_xboole_0(B_35,k4_xboole_0(k3_xboole_0(A_34,B_35),B_9))) = k3_xboole_0(k3_xboole_0(A_34,B_35),B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_12])).

tff(c_7172,plain,(
    ! [A_159,B_160,B_161] : k3_xboole_0(A_159,k4_xboole_0(B_160,k3_xboole_0(A_159,k4_xboole_0(B_160,B_161)))) = k3_xboole_0(k3_xboole_0(A_159,B_160),B_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_180])).

tff(c_7399,plain,(
    ! [B_160,B_161] : k3_xboole_0(k4_xboole_0(B_160,B_161),k4_xboole_0(B_160,k4_xboole_0(B_160,B_161))) = k3_xboole_0(k3_xboole_0(k4_xboole_0(B_160,B_161),B_160),B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_7172])).

tff(c_7723,plain,(
    ! [B_165,B_166] : k3_xboole_0(k3_xboole_0(k4_xboole_0(B_165,B_166),B_165),B_166) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2720,c_12,c_7399])).

tff(c_114,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_173,plain,(
    ! [A_34,B_35] : k3_xboole_0(A_34,k4_xboole_0(B_35,k3_xboole_0(A_34,B_35))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_114])).

tff(c_196,plain,(
    ! [A_31,C_36] : k3_xboole_0(A_31,k4_xboole_0(A_31,C_36)) = k4_xboole_0(A_31,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_166])).

tff(c_105,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,k4_xboole_0(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_90])).

tff(c_3244,plain,(
    ! [A_110,B_111] : k4_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_105])).

tff(c_3332,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(B_35,k3_xboole_0(A_34,B_35))) = k4_xboole_0(A_34,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_3244])).

tff(c_3388,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(B_35,k3_xboole_0(A_34,B_35))) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3332])).

tff(c_7741,plain,(
    ! [B_165,B_166] : k4_xboole_0(k3_xboole_0(k4_xboole_0(B_165,B_166),B_165),k4_xboole_0(B_166,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(B_165,B_166),B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_7723,c_3388])).

tff(c_8066,plain,(
    ! [B_169,B_170] : k3_xboole_0(k4_xboole_0(B_169,B_170),B_169) = k4_xboole_0(B_169,B_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_14,c_8,c_7741])).

tff(c_8256,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(k3_xboole_0(A_8,B_9),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8066])).

tff(c_8317,plain,(
    ! [A_8,B_9] : k3_xboole_0(k3_xboole_0(A_8,B_9),A_8) = k3_xboole_0(A_8,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8256])).

tff(c_26602,plain,(
    ! [C_328,B_327] : k3_xboole_0(C_328,k3_xboole_0(B_327,C_328)) = k3_xboole_0(C_328,B_327) ),
    inference(superposition,[status(thm),theory(equality)],[c_26520,c_8317])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_4451,plain,(
    ! [A_126,B_127,C_128] : k4_xboole_0(k3_xboole_0(A_126,B_127),k3_xboole_0(A_126,k4_xboole_0(B_127,C_128))) = k3_xboole_0(k3_xboole_0(A_126,B_127),C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_12])).

tff(c_4658,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4451])).

tff(c_4710,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4658])).

tff(c_5517,plain,(
    ! [A_8,B_9,C_49] : k3_xboole_0(k3_xboole_0(A_8,B_9),C_49) = k3_xboole_0(A_8,k3_xboole_0(B_9,C_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16,c_12,c_5434])).

tff(c_14633,plain,(
    ! [A_254,B_255] : k3_xboole_0(k3_xboole_0(A_254,B_255),A_254) = k3_xboole_0(A_254,B_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8256])).

tff(c_373,plain,(
    ! [A_42,B_43,C_44] : r1_xboole_0(k3_xboole_0(A_42,k4_xboole_0(B_43,C_44)),C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_18])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_408,plain,(
    ! [A_42,B_43,C_44] : k3_xboole_0(k3_xboole_0(A_42,k4_xboole_0(B_43,C_44)),C_44) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_373,c_2])).

tff(c_14744,plain,(
    ! [B_43,C_44,B_255] : k3_xboole_0(k3_xboole_0(k4_xboole_0(B_43,C_44),B_255),C_44) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14633,c_408])).

tff(c_31946,plain,(
    ! [B_356,C_357,B_358] : k3_xboole_0(k4_xboole_0(B_356,C_357),k3_xboole_0(B_358,C_357)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14744,c_26520])).

tff(c_7912,plain,(
    ! [B_165,B_166] : k3_xboole_0(k4_xboole_0(B_165,B_166),B_165) = k4_xboole_0(B_165,B_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_14,c_8,c_7741])).

tff(c_32480,plain,(
    ! [B_359,C_360] : k4_xboole_0(k3_xboole_0(B_359,C_360),C_360) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31946,c_7912])).

tff(c_46244,plain,(
    ! [A_424,B_425,C_426] : k4_xboole_0(k3_xboole_0(A_424,k3_xboole_0(B_425,C_426)),C_426) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5517,c_32480])).

tff(c_48004,plain,(
    ! [A_432] : k4_xboole_0(k3_xboole_0(A_432,k3_xboole_0('#skF_1','#skF_2')),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4710,c_46244])).

tff(c_48214,plain,(
    k4_xboole_0(k3_xboole_0('#skF_2','#skF_1'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26602,c_48004])).

tff(c_48483,plain,(
    k4_xboole_0(k3_xboole_0('#skF_2','#skF_1'),'#skF_3') = k3_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48214,c_7912])).

tff(c_48594,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_14,c_48483])).

tff(c_48596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_48594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.12/5.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.12/5.53  
% 11.12/5.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.12/5.53  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.12/5.53  
% 11.12/5.53  %Foreground sorts:
% 11.12/5.53  
% 11.12/5.53  
% 11.12/5.53  %Background operators:
% 11.12/5.53  
% 11.12/5.53  
% 11.12/5.53  %Foreground operators:
% 11.12/5.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.12/5.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.12/5.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.12/5.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.12/5.53  tff('#skF_2', type, '#skF_2': $i).
% 11.12/5.53  tff('#skF_3', type, '#skF_3': $i).
% 11.12/5.53  tff('#skF_1', type, '#skF_1': $i).
% 11.12/5.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.12/5.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.12/5.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.12/5.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.12/5.53  
% 11.20/5.55  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.20/5.55  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.20/5.55  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.20/5.55  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.20/5.55  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.20/5.55  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.20/5.55  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.20/5.55  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 11.20/5.55  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.20/5.55  tff(c_43, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k3_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.20/5.55  tff(c_20, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.20/5.55  tff(c_47, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_43, c_20])).
% 11.20/5.55  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.20/5.55  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.20/5.55  tff(c_90, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.20/5.55  tff(c_111, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_90])).
% 11.20/5.55  tff(c_115, plain, (![A_31]: (k4_xboole_0(A_31, A_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 11.20/5.55  tff(c_18, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.20/5.55  tff(c_49, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.20/5.55  tff(c_65, plain, (![A_16, B_17]: (k3_xboole_0(k4_xboole_0(A_16, B_17), B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_49])).
% 11.20/5.55  tff(c_123, plain, (![A_31]: (k3_xboole_0(k1_xboole_0, A_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_115, c_65])).
% 11.20/5.55  tff(c_14, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.20/5.55  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.20/5.55  tff(c_16, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15))=k4_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.20/5.55  tff(c_489, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k4_xboole_0(A_47, B_48), C_49)=k4_xboole_0(A_47, k2_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.20/5.55  tff(c_547, plain, (![A_8, B_9, C_49]: (k4_xboole_0(A_8, k2_xboole_0(k4_xboole_0(A_8, B_9), C_49))=k4_xboole_0(k3_xboole_0(A_8, B_9), C_49))), inference(superposition, [status(thm), theory('equality')], [c_12, c_489])).
% 11.20/5.55  tff(c_567, plain, (![A_8, B_9, C_49]: (k4_xboole_0(A_8, k2_xboole_0(k4_xboole_0(A_8, B_9), C_49))=k3_xboole_0(A_8, k4_xboole_0(B_9, C_49)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_547])).
% 11.20/5.55  tff(c_10, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k4_xboole_0(A_5, B_6), C_7)=k4_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.20/5.55  tff(c_551, plain, (![A_47, B_48, B_9]: (k4_xboole_0(A_47, k2_xboole_0(B_48, k4_xboole_0(k4_xboole_0(A_47, B_48), B_9)))=k3_xboole_0(k4_xboole_0(A_47, B_48), B_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_489])).
% 11.20/5.55  tff(c_5318, plain, (![A_137, B_138, B_139]: (k4_xboole_0(A_137, k2_xboole_0(B_138, k4_xboole_0(A_137, k2_xboole_0(B_138, B_139))))=k3_xboole_0(k4_xboole_0(A_137, B_138), B_139))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_551])).
% 11.20/5.55  tff(c_5434, plain, (![A_8, B_9, C_49]: (k4_xboole_0(A_8, k2_xboole_0(k4_xboole_0(A_8, B_9), k3_xboole_0(A_8, k4_xboole_0(B_9, C_49))))=k3_xboole_0(k4_xboole_0(A_8, k4_xboole_0(A_8, B_9)), C_49))), inference(superposition, [status(thm), theory('equality')], [c_567, c_5318])).
% 11.20/5.55  tff(c_26520, plain, (![A_326, B_327, C_328]: (k3_xboole_0(k3_xboole_0(A_326, B_327), C_328)=k3_xboole_0(A_326, k3_xboole_0(B_327, C_328)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16, c_12, c_5434])).
% 11.20/5.55  tff(c_120, plain, (![A_31]: (k4_xboole_0(A_31, k1_xboole_0)=k3_xboole_0(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_115, c_12])).
% 11.20/5.55  tff(c_138, plain, (![A_31]: (k3_xboole_0(A_31, A_31)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_120])).
% 11.20/5.55  tff(c_166, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k3_xboole_0(A_34, B_35), C_36)=k3_xboole_0(A_34, k4_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.20/5.55  tff(c_2623, plain, (![A_96, C_97]: (k3_xboole_0(A_96, k4_xboole_0(A_96, C_97))=k4_xboole_0(A_96, C_97))), inference(superposition, [status(thm), theory('equality')], [c_138, c_166])).
% 11.20/5.55  tff(c_99, plain, (![A_29, B_30]: (k3_xboole_0(k3_xboole_0(A_29, B_30), k4_xboole_0(A_29, B_30))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_65])).
% 11.20/5.55  tff(c_2656, plain, (![A_96, C_97]: (k3_xboole_0(k4_xboole_0(A_96, C_97), k4_xboole_0(A_96, k4_xboole_0(A_96, C_97)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2623, c_99])).
% 11.20/5.55  tff(c_2720, plain, (![A_96, C_97]: (k3_xboole_0(k4_xboole_0(A_96, C_97), k3_xboole_0(A_96, C_97))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2656])).
% 11.20/5.55  tff(c_180, plain, (![A_34, B_35, B_9]: (k3_xboole_0(A_34, k4_xboole_0(B_35, k4_xboole_0(k3_xboole_0(A_34, B_35), B_9)))=k3_xboole_0(k3_xboole_0(A_34, B_35), B_9))), inference(superposition, [status(thm), theory('equality')], [c_166, c_12])).
% 11.20/5.55  tff(c_7172, plain, (![A_159, B_160, B_161]: (k3_xboole_0(A_159, k4_xboole_0(B_160, k3_xboole_0(A_159, k4_xboole_0(B_160, B_161))))=k3_xboole_0(k3_xboole_0(A_159, B_160), B_161))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_180])).
% 11.20/5.55  tff(c_7399, plain, (![B_160, B_161]: (k3_xboole_0(k4_xboole_0(B_160, B_161), k4_xboole_0(B_160, k4_xboole_0(B_160, B_161)))=k3_xboole_0(k3_xboole_0(k4_xboole_0(B_160, B_161), B_160), B_161))), inference(superposition, [status(thm), theory('equality')], [c_138, c_7172])).
% 11.20/5.55  tff(c_7723, plain, (![B_165, B_166]: (k3_xboole_0(k3_xboole_0(k4_xboole_0(B_165, B_166), B_165), B_166)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2720, c_12, c_7399])).
% 11.20/5.55  tff(c_114, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 11.20/5.55  tff(c_173, plain, (![A_34, B_35]: (k3_xboole_0(A_34, k4_xboole_0(B_35, k3_xboole_0(A_34, B_35)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_114])).
% 11.20/5.55  tff(c_196, plain, (![A_31, C_36]: (k3_xboole_0(A_31, k4_xboole_0(A_31, C_36))=k4_xboole_0(A_31, C_36))), inference(superposition, [status(thm), theory('equality')], [c_138, c_166])).
% 11.20/5.55  tff(c_105, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k3_xboole_0(A_8, k4_xboole_0(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_90])).
% 11.20/5.55  tff(c_3244, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_105])).
% 11.20/5.55  tff(c_3332, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(B_35, k3_xboole_0(A_34, B_35)))=k4_xboole_0(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_173, c_3244])).
% 11.20/5.55  tff(c_3388, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(B_35, k3_xboole_0(A_34, B_35)))=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3332])).
% 11.20/5.55  tff(c_7741, plain, (![B_165, B_166]: (k4_xboole_0(k3_xboole_0(k4_xboole_0(B_165, B_166), B_165), k4_xboole_0(B_166, k1_xboole_0))=k3_xboole_0(k4_xboole_0(B_165, B_166), B_165))), inference(superposition, [status(thm), theory('equality')], [c_7723, c_3388])).
% 11.20/5.55  tff(c_8066, plain, (![B_169, B_170]: (k3_xboole_0(k4_xboole_0(B_169, B_170), B_169)=k4_xboole_0(B_169, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_14, c_8, c_7741])).
% 11.20/5.55  tff(c_8256, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(k3_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8066])).
% 11.20/5.55  tff(c_8317, plain, (![A_8, B_9]: (k3_xboole_0(k3_xboole_0(A_8, B_9), A_8)=k3_xboole_0(A_8, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8256])).
% 11.20/5.55  tff(c_26602, plain, (![C_328, B_327]: (k3_xboole_0(C_328, k3_xboole_0(B_327, C_328))=k3_xboole_0(C_328, B_327))), inference(superposition, [status(thm), theory('equality')], [c_26520, c_8317])).
% 11.20/5.55  tff(c_22, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.20/5.55  tff(c_66, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_49])).
% 11.20/5.55  tff(c_4451, plain, (![A_126, B_127, C_128]: (k4_xboole_0(k3_xboole_0(A_126, B_127), k3_xboole_0(A_126, k4_xboole_0(B_127, C_128)))=k3_xboole_0(k3_xboole_0(A_126, B_127), C_128))), inference(superposition, [status(thm), theory('equality')], [c_166, c_12])).
% 11.20/5.55  tff(c_4658, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66, c_4451])).
% 11.20/5.55  tff(c_4710, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4658])).
% 11.20/5.55  tff(c_5517, plain, (![A_8, B_9, C_49]: (k3_xboole_0(k3_xboole_0(A_8, B_9), C_49)=k3_xboole_0(A_8, k3_xboole_0(B_9, C_49)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16, c_12, c_5434])).
% 11.20/5.55  tff(c_14633, plain, (![A_254, B_255]: (k3_xboole_0(k3_xboole_0(A_254, B_255), A_254)=k3_xboole_0(A_254, B_255))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8256])).
% 11.20/5.55  tff(c_373, plain, (![A_42, B_43, C_44]: (r1_xboole_0(k3_xboole_0(A_42, k4_xboole_0(B_43, C_44)), C_44))), inference(superposition, [status(thm), theory('equality')], [c_166, c_18])).
% 11.20/5.55  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.20/5.55  tff(c_408, plain, (![A_42, B_43, C_44]: (k3_xboole_0(k3_xboole_0(A_42, k4_xboole_0(B_43, C_44)), C_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_373, c_2])).
% 11.20/5.55  tff(c_14744, plain, (![B_43, C_44, B_255]: (k3_xboole_0(k3_xboole_0(k4_xboole_0(B_43, C_44), B_255), C_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14633, c_408])).
% 11.20/5.55  tff(c_31946, plain, (![B_356, C_357, B_358]: (k3_xboole_0(k4_xboole_0(B_356, C_357), k3_xboole_0(B_358, C_357))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14744, c_26520])).
% 11.20/5.55  tff(c_7912, plain, (![B_165, B_166]: (k3_xboole_0(k4_xboole_0(B_165, B_166), B_165)=k4_xboole_0(B_165, B_166))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_14, c_8, c_7741])).
% 11.20/5.55  tff(c_32480, plain, (![B_359, C_360]: (k4_xboole_0(k3_xboole_0(B_359, C_360), C_360)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_31946, c_7912])).
% 11.20/5.55  tff(c_46244, plain, (![A_424, B_425, C_426]: (k4_xboole_0(k3_xboole_0(A_424, k3_xboole_0(B_425, C_426)), C_426)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5517, c_32480])).
% 11.20/5.55  tff(c_48004, plain, (![A_432]: (k4_xboole_0(k3_xboole_0(A_432, k3_xboole_0('#skF_1', '#skF_2')), '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4710, c_46244])).
% 11.20/5.55  tff(c_48214, plain, (k4_xboole_0(k3_xboole_0('#skF_2', '#skF_1'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26602, c_48004])).
% 11.20/5.55  tff(c_48483, plain, (k4_xboole_0(k3_xboole_0('#skF_2', '#skF_1'), '#skF_3')=k3_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48214, c_7912])).
% 11.20/5.55  tff(c_48594, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123, c_14, c_48483])).
% 11.20/5.55  tff(c_48596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_48594])).
% 11.20/5.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.20/5.55  
% 11.20/5.55  Inference rules
% 11.20/5.55  ----------------------
% 11.20/5.55  #Ref     : 0
% 11.20/5.55  #Sup     : 12105
% 11.20/5.55  #Fact    : 0
% 11.20/5.55  #Define  : 0
% 11.20/5.55  #Split   : 0
% 11.20/5.55  #Chain   : 0
% 11.20/5.55  #Close   : 0
% 11.20/5.55  
% 11.20/5.55  Ordering : KBO
% 11.20/5.55  
% 11.20/5.55  Simplification rules
% 11.20/5.55  ----------------------
% 11.20/5.55  #Subsume      : 0
% 11.20/5.55  #Demod        : 14550
% 11.20/5.55  #Tautology    : 8966
% 11.20/5.55  #SimpNegUnit  : 1
% 11.20/5.55  #BackRed      : 29
% 11.20/5.55  
% 11.20/5.55  #Partial instantiations: 0
% 11.20/5.55  #Strategies tried      : 1
% 11.20/5.55  
% 11.20/5.55  Timing (in seconds)
% 11.20/5.55  ----------------------
% 11.20/5.56  Preprocessing        : 0.26
% 11.20/5.56  Parsing              : 0.14
% 11.20/5.56  CNF conversion       : 0.02
% 11.20/5.56  Main loop            : 4.50
% 11.20/5.56  Inferencing          : 0.77
% 11.20/5.56  Reduction            : 2.68
% 11.20/5.56  Demodulation         : 2.41
% 11.20/5.56  BG Simplification    : 0.09
% 11.20/5.56  Subsumption          : 0.74
% 11.20/5.56  Abstraction          : 0.16
% 11.20/5.56  MUC search           : 0.00
% 11.20/5.56  Cooper               : 0.00
% 11.20/5.56  Total                : 4.80
% 11.20/5.56  Index Insertion      : 0.00
% 11.20/5.56  Index Deletion       : 0.00
% 11.20/5.56  Index Matching       : 0.00
% 11.20/5.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
