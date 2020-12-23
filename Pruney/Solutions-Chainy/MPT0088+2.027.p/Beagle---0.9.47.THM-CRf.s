%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:23 EST 2020

% Result     : Theorem 11.32s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 736 expanded)
%              Number of leaves         :   20 ( 256 expanded)
%              Depth                    :   20
%              Number of atoms          :   90 ( 735 expanded)
%              Number of equality atoms :   73 ( 697 expanded)
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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_456,plain,(
    ! [A_46,B_47,C_48] : k2_xboole_0(k4_xboole_0(A_46,B_47),k3_xboole_0(A_46,C_48)) = k4_xboole_0(A_46,k4_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_504,plain,(
    ! [A_3,B_47] : k4_xboole_0(A_3,k4_xboole_0(B_47,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_3,B_47),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_456])).

tff(c_1382,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),k1_xboole_0) = k4_xboole_0(A_66,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_504])).

tff(c_1445,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1382])).

tff(c_1466,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1445])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_228,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k4_xboole_0(A_37,B_38),C_39) = k4_xboole_0(A_37,k2_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_248,plain,(
    ! [A_37,B_38,B_11] : k4_xboole_0(A_37,k2_xboole_0(B_38,k4_xboole_0(k4_xboole_0(A_37,B_38),B_11))) = k3_xboole_0(k4_xboole_0(A_37,B_38),B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_14])).

tff(c_289,plain,(
    ! [A_37,B_38,B_11] : k4_xboole_0(A_37,k2_xboole_0(B_38,k4_xboole_0(A_37,k2_xboole_0(B_38,B_11)))) = k3_xboole_0(k4_xboole_0(A_37,B_38),B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_248])).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5663,plain,(
    ! [A_144,B_145,B_146] : k4_xboole_0(A_144,k2_xboole_0(B_145,k4_xboole_0(A_144,k2_xboole_0(B_145,B_146)))) = k3_xboole_0(k4_xboole_0(A_144,B_145),B_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_248])).

tff(c_5887,plain,(
    ! [A_144,A_4,B_5] : k4_xboole_0(A_144,k2_xboole_0(A_4,k4_xboole_0(A_144,k2_xboole_0(A_4,B_5)))) = k3_xboole_0(k4_xboole_0(A_144,A_4),k4_xboole_0(B_5,A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5663])).

tff(c_43315,plain,(
    ! [A_425,A_426,B_427] : k3_xboole_0(k4_xboole_0(A_425,A_426),k4_xboole_0(B_427,A_426)) = k3_xboole_0(k4_xboole_0(A_425,A_426),B_427) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_5887])).

tff(c_90,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_114,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_515,plain,(
    ! [A_3,B_47] : k2_xboole_0(k4_xboole_0(A_3,B_47),k1_xboole_0) = k4_xboole_0(A_3,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_504])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_501,plain,(
    ! [B_47] : k4_xboole_0('#skF_1',k4_xboole_0(B_47,k4_xboole_0('#skF_2','#skF_3'))) = k2_xboole_0(k4_xboole_0('#skF_1',B_47),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_456])).

tff(c_1606,plain,(
    ! [B_72] : k4_xboole_0('#skF_1',k4_xboole_0(B_72,k4_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0('#skF_1',B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_501])).

tff(c_1656,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1606])).

tff(c_1673,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1656])).

tff(c_166,plain,(
    ! [A_33,B_34] : k2_xboole_0(A_33,k4_xboole_0(B_34,A_33)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2888,plain,(
    ! [A_100,B_101] : k2_xboole_0(k4_xboole_0(A_100,B_101),k3_xboole_0(A_100,B_101)) = k2_xboole_0(k4_xboole_0(A_100,B_101),A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_166])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k4_xboole_0(A_12,B_13),k3_xboole_0(A_12,C_14)) = k4_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2906,plain,(
    ! [A_100,B_101] : k4_xboole_0(A_100,k4_xboole_0(B_101,B_101)) = k2_xboole_0(k4_xboole_0(A_100,B_101),A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_2888,c_16])).

tff(c_3011,plain,(
    ! [A_102,B_103] : k2_xboole_0(k4_xboole_0(A_102,B_103),A_102) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_114,c_2906])).

tff(c_868,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k2_xboole_0(B_61,k1_xboole_0)) = k4_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_228])).

tff(c_241,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(B_38,k4_xboole_0(A_37,B_38))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_114])).

tff(c_288,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(B_38,A_37)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_241])).

tff(c_896,plain,(
    ! [B_61] : k4_xboole_0(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_288])).

tff(c_267,plain,(
    ! [A_6,C_39] : k4_xboole_0(A_6,k2_xboole_0(A_6,C_39)) = k4_xboole_0(k1_xboole_0,C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_228])).

tff(c_2617,plain,(
    ! [A_6,C_39] : k4_xboole_0(A_6,k2_xboole_0(A_6,C_39)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_267])).

tff(c_3247,plain,(
    ! [A_107,B_108] : k4_xboole_0(k4_xboole_0(A_107,B_108),A_107) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3011,c_2617])).

tff(c_3298,plain,(
    ! [A_107,B_108] : k2_xboole_0(A_107,k4_xboole_0(A_107,B_108)) = k2_xboole_0(A_107,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_8])).

tff(c_3373,plain,(
    ! [A_107,B_108] : k2_xboole_0(A_107,k4_xboole_0(A_107,B_108)) = A_107 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_3298])).

tff(c_115,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_120,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_14])).

tff(c_138,plain,(
    ! [A_30] : k3_xboole_0(A_30,A_30) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_120])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_690,plain,(
    ! [A_53,B_54,C_55] : r1_xboole_0(k4_xboole_0(A_53,k2_xboole_0(B_54,C_55)),C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_18])).

tff(c_20887,plain,(
    ! [A_292,A_293,B_294,C_295] : r1_xboole_0(k4_xboole_0(A_292,k4_xboole_0(A_293,k4_xboole_0(B_294,C_295))),k3_xboole_0(A_293,C_295)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_690])).

tff(c_21241,plain,(
    ! [A_296,A_297,B_298] : r1_xboole_0(k4_xboole_0(A_296,k4_xboole_0(A_297,k4_xboole_0(B_298,A_297))),A_297) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_20887])).

tff(c_21433,plain,(
    ! [A_299,B_300] : r1_xboole_0(k3_xboole_0(A_299,k4_xboole_0(B_300,A_299)),A_299) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_21241])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_21569,plain,(
    ! [A_301,B_302] : k3_xboole_0(k3_xboole_0(A_301,k4_xboole_0(B_302,A_301)),A_301) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21433,c_2])).

tff(c_5876,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(B_38,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_37,B_38),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_5663])).

tff(c_6156,plain,(
    ! [A_150,B_151] : k3_xboole_0(k4_xboole_0(A_150,B_151),A_150) = k4_xboole_0(A_150,B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_5876])).

tff(c_6286,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(k3_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6156])).

tff(c_6338,plain,(
    ! [A_10,B_11] : k3_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k3_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6286])).

tff(c_21860,plain,(
    ! [A_303,B_304] : k3_xboole_0(A_303,k4_xboole_0(B_304,A_303)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21569,c_6338])).

tff(c_2986,plain,(
    ! [A_100,B_101] : k2_xboole_0(k4_xboole_0(A_100,B_101),A_100) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_114,c_2906])).

tff(c_178,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_166])).

tff(c_3010,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2986,c_178])).

tff(c_23670,plain,(
    ! [A_311,B_312] : k2_xboole_0(k4_xboole_0(A_311,k4_xboole_0(B_312,A_311)),k1_xboole_0) = A_311 ),
    inference(superposition,[status(thm),theory(equality)],[c_21860,c_3010])).

tff(c_2618,plain,(
    ! [A_95,C_96] : k4_xboole_0(A_95,k2_xboole_0(A_95,C_96)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_267])).

tff(c_2662,plain,(
    ! [A_95,C_96] : k2_xboole_0(k2_xboole_0(A_95,C_96),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_95,C_96),A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_2618,c_8])).

tff(c_2714,plain,(
    ! [A_95,C_96] : k2_xboole_0(k2_xboole_0(A_95,C_96),A_95) = k2_xboole_0(A_95,C_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_2662])).

tff(c_23730,plain,(
    ! [A_311,B_312] : k2_xboole_0(k4_xboole_0(A_311,k4_xboole_0(B_312,A_311)),k1_xboole_0) = k2_xboole_0(A_311,k4_xboole_0(A_311,k4_xboole_0(B_312,A_311))) ),
    inference(superposition,[status(thm),theory(equality)],[c_23670,c_2714])).

tff(c_24002,plain,(
    ! [A_313,B_314] : k4_xboole_0(A_313,k4_xboole_0(B_314,A_313)) = A_313 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3373,c_1466,c_23730])).

tff(c_24299,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_24002])).

tff(c_22816,plain,(
    ! [C_307,A_308,B_309] : k3_xboole_0(C_307,k4_xboole_0(A_308,k2_xboole_0(B_309,C_307))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_21860])).

tff(c_23095,plain,(
    ! [A_107,B_108,A_308] : k3_xboole_0(k4_xboole_0(A_107,B_108),k4_xboole_0(A_308,A_107)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3373,c_22816])).

tff(c_30674,plain,(
    ! [B_108] : k3_xboole_0(k4_xboole_0('#skF_1',B_108),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24299,c_23095])).

tff(c_43359,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43315,c_30674])).

tff(c_44169,plain,(
    k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2'),k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_43359,c_3010])).

tff(c_44234,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_12,c_44169])).

tff(c_24403,plain,(
    ! [A_315,B_316] : r1_xboole_0(A_315,k4_xboole_0(B_316,A_315)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24002,c_18])).

tff(c_24502,plain,(
    ! [C_9,A_7,B_8] : r1_xboole_0(C_9,k4_xboole_0(A_7,k2_xboole_0(B_8,C_9))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_24403])).

tff(c_45243,plain,(
    r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44234,c_24502])).

tff(c_45439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_45243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:39:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.32/5.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.46/5.63  
% 11.46/5.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.48/5.64  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.48/5.64  
% 11.48/5.64  %Foreground sorts:
% 11.48/5.64  
% 11.48/5.64  
% 11.48/5.64  %Background operators:
% 11.48/5.64  
% 11.48/5.64  
% 11.48/5.64  %Foreground operators:
% 11.48/5.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.48/5.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.48/5.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.48/5.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.48/5.64  tff('#skF_2', type, '#skF_2': $i).
% 11.48/5.64  tff('#skF_3', type, '#skF_3': $i).
% 11.48/5.64  tff('#skF_1', type, '#skF_1': $i).
% 11.48/5.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.48/5.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.48/5.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.48/5.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.48/5.64  
% 11.48/5.66  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.48/5.66  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.48/5.66  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.48/5.66  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 11.48/5.66  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.48/5.66  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.48/5.66  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.48/5.66  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.48/5.66  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.48/5.66  tff(c_20, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.48/5.66  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.48/5.66  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.48/5.66  tff(c_456, plain, (![A_46, B_47, C_48]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k3_xboole_0(A_46, C_48))=k4_xboole_0(A_46, k4_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.48/5.66  tff(c_504, plain, (![A_3, B_47]: (k4_xboole_0(A_3, k4_xboole_0(B_47, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_3, B_47), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_456])).
% 11.48/5.66  tff(c_1382, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k1_xboole_0)=k4_xboole_0(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_504])).
% 11.48/5.66  tff(c_1445, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1382])).
% 11.48/5.66  tff(c_1466, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1445])).
% 11.48/5.66  tff(c_12, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.48/5.66  tff(c_228, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k4_xboole_0(A_37, B_38), C_39)=k4_xboole_0(A_37, k2_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.48/5.66  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.48/5.66  tff(c_248, plain, (![A_37, B_38, B_11]: (k4_xboole_0(A_37, k2_xboole_0(B_38, k4_xboole_0(k4_xboole_0(A_37, B_38), B_11)))=k3_xboole_0(k4_xboole_0(A_37, B_38), B_11))), inference(superposition, [status(thm), theory('equality')], [c_228, c_14])).
% 11.48/5.66  tff(c_289, plain, (![A_37, B_38, B_11]: (k4_xboole_0(A_37, k2_xboole_0(B_38, k4_xboole_0(A_37, k2_xboole_0(B_38, B_11))))=k3_xboole_0(k4_xboole_0(A_37, B_38), B_11))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_248])).
% 11.48/5.66  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.48/5.66  tff(c_5663, plain, (![A_144, B_145, B_146]: (k4_xboole_0(A_144, k2_xboole_0(B_145, k4_xboole_0(A_144, k2_xboole_0(B_145, B_146))))=k3_xboole_0(k4_xboole_0(A_144, B_145), B_146))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_248])).
% 11.48/5.66  tff(c_5887, plain, (![A_144, A_4, B_5]: (k4_xboole_0(A_144, k2_xboole_0(A_4, k4_xboole_0(A_144, k2_xboole_0(A_4, B_5))))=k3_xboole_0(k4_xboole_0(A_144, A_4), k4_xboole_0(B_5, A_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_5663])).
% 11.48/5.66  tff(c_43315, plain, (![A_425, A_426, B_427]: (k3_xboole_0(k4_xboole_0(A_425, A_426), k4_xboole_0(B_427, A_426))=k3_xboole_0(k4_xboole_0(A_425, A_426), B_427))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_5887])).
% 11.48/5.66  tff(c_90, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.48/5.66  tff(c_111, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 11.48/5.66  tff(c_114, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 11.48/5.66  tff(c_515, plain, (![A_3, B_47]: (k2_xboole_0(k4_xboole_0(A_3, B_47), k1_xboole_0)=k4_xboole_0(A_3, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_504])).
% 11.48/5.66  tff(c_22, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.48/5.66  tff(c_49, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.48/5.66  tff(c_66, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_49])).
% 11.48/5.66  tff(c_501, plain, (![B_47]: (k4_xboole_0('#skF_1', k4_xboole_0(B_47, k4_xboole_0('#skF_2', '#skF_3')))=k2_xboole_0(k4_xboole_0('#skF_1', B_47), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_456])).
% 11.48/5.66  tff(c_1606, plain, (![B_72]: (k4_xboole_0('#skF_1', k4_xboole_0(B_72, k4_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0('#skF_1', B_72))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_501])).
% 11.48/5.66  tff(c_1656, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_114, c_1606])).
% 11.48/5.66  tff(c_1673, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1656])).
% 11.48/5.66  tff(c_166, plain, (![A_33, B_34]: (k2_xboole_0(A_33, k4_xboole_0(B_34, A_33))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.48/5.66  tff(c_2888, plain, (![A_100, B_101]: (k2_xboole_0(k4_xboole_0(A_100, B_101), k3_xboole_0(A_100, B_101))=k2_xboole_0(k4_xboole_0(A_100, B_101), A_100))), inference(superposition, [status(thm), theory('equality')], [c_14, c_166])).
% 11.48/5.66  tff(c_16, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k3_xboole_0(A_12, C_14))=k4_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.48/5.66  tff(c_2906, plain, (![A_100, B_101]: (k4_xboole_0(A_100, k4_xboole_0(B_101, B_101))=k2_xboole_0(k4_xboole_0(A_100, B_101), A_100))), inference(superposition, [status(thm), theory('equality')], [c_2888, c_16])).
% 11.48/5.66  tff(c_3011, plain, (![A_102, B_103]: (k2_xboole_0(k4_xboole_0(A_102, B_103), A_102)=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_114, c_2906])).
% 11.48/5.66  tff(c_868, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k2_xboole_0(B_61, k1_xboole_0))=k4_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_10, c_228])).
% 11.48/5.66  tff(c_241, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(B_38, k4_xboole_0(A_37, B_38)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_228, c_114])).
% 11.48/5.66  tff(c_288, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(B_38, A_37))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_241])).
% 11.48/5.66  tff(c_896, plain, (![B_61]: (k4_xboole_0(k1_xboole_0, B_61)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_868, c_288])).
% 11.48/5.66  tff(c_267, plain, (![A_6, C_39]: (k4_xboole_0(A_6, k2_xboole_0(A_6, C_39))=k4_xboole_0(k1_xboole_0, C_39))), inference(superposition, [status(thm), theory('equality')], [c_114, c_228])).
% 11.48/5.66  tff(c_2617, plain, (![A_6, C_39]: (k4_xboole_0(A_6, k2_xboole_0(A_6, C_39))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_896, c_267])).
% 11.48/5.66  tff(c_3247, plain, (![A_107, B_108]: (k4_xboole_0(k4_xboole_0(A_107, B_108), A_107)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3011, c_2617])).
% 11.48/5.66  tff(c_3298, plain, (![A_107, B_108]: (k2_xboole_0(A_107, k4_xboole_0(A_107, B_108))=k2_xboole_0(A_107, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3247, c_8])).
% 11.48/5.66  tff(c_3373, plain, (![A_107, B_108]: (k2_xboole_0(A_107, k4_xboole_0(A_107, B_108))=A_107)), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_3298])).
% 11.48/5.66  tff(c_115, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 11.48/5.66  tff(c_120, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_115, c_14])).
% 11.48/5.66  tff(c_138, plain, (![A_30]: (k3_xboole_0(A_30, A_30)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_120])).
% 11.48/5.66  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.48/5.66  tff(c_690, plain, (![A_53, B_54, C_55]: (r1_xboole_0(k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)), C_55))), inference(superposition, [status(thm), theory('equality')], [c_228, c_18])).
% 11.48/5.66  tff(c_20887, plain, (![A_292, A_293, B_294, C_295]: (r1_xboole_0(k4_xboole_0(A_292, k4_xboole_0(A_293, k4_xboole_0(B_294, C_295))), k3_xboole_0(A_293, C_295)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_690])).
% 11.48/5.66  tff(c_21241, plain, (![A_296, A_297, B_298]: (r1_xboole_0(k4_xboole_0(A_296, k4_xboole_0(A_297, k4_xboole_0(B_298, A_297))), A_297))), inference(superposition, [status(thm), theory('equality')], [c_138, c_20887])).
% 11.48/5.66  tff(c_21433, plain, (![A_299, B_300]: (r1_xboole_0(k3_xboole_0(A_299, k4_xboole_0(B_300, A_299)), A_299))), inference(superposition, [status(thm), theory('equality')], [c_14, c_21241])).
% 11.48/5.66  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.48/5.66  tff(c_21569, plain, (![A_301, B_302]: (k3_xboole_0(k3_xboole_0(A_301, k4_xboole_0(B_302, A_301)), A_301)=k1_xboole_0)), inference(resolution, [status(thm)], [c_21433, c_2])).
% 11.48/5.66  tff(c_5876, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(B_38, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_37, B_38), A_37))), inference(superposition, [status(thm), theory('equality')], [c_288, c_5663])).
% 11.48/5.66  tff(c_6156, plain, (![A_150, B_151]: (k3_xboole_0(k4_xboole_0(A_150, B_151), A_150)=k4_xboole_0(A_150, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_5876])).
% 11.48/5.66  tff(c_6286, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(k3_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6156])).
% 11.48/5.66  tff(c_6338, plain, (![A_10, B_11]: (k3_xboole_0(k3_xboole_0(A_10, B_11), A_10)=k3_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6286])).
% 11.48/5.66  tff(c_21860, plain, (![A_303, B_304]: (k3_xboole_0(A_303, k4_xboole_0(B_304, A_303))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_21569, c_6338])).
% 11.48/5.66  tff(c_2986, plain, (![A_100, B_101]: (k2_xboole_0(k4_xboole_0(A_100, B_101), A_100)=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_114, c_2906])).
% 11.48/5.66  tff(c_178, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=k2_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_166])).
% 11.48/5.66  tff(c_3010, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_2986, c_178])).
% 11.48/5.66  tff(c_23670, plain, (![A_311, B_312]: (k2_xboole_0(k4_xboole_0(A_311, k4_xboole_0(B_312, A_311)), k1_xboole_0)=A_311)), inference(superposition, [status(thm), theory('equality')], [c_21860, c_3010])).
% 11.48/5.66  tff(c_2618, plain, (![A_95, C_96]: (k4_xboole_0(A_95, k2_xboole_0(A_95, C_96))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_896, c_267])).
% 11.48/5.66  tff(c_2662, plain, (![A_95, C_96]: (k2_xboole_0(k2_xboole_0(A_95, C_96), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_95, C_96), A_95))), inference(superposition, [status(thm), theory('equality')], [c_2618, c_8])).
% 11.48/5.66  tff(c_2714, plain, (![A_95, C_96]: (k2_xboole_0(k2_xboole_0(A_95, C_96), A_95)=k2_xboole_0(A_95, C_96))), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_2662])).
% 11.48/5.66  tff(c_23730, plain, (![A_311, B_312]: (k2_xboole_0(k4_xboole_0(A_311, k4_xboole_0(B_312, A_311)), k1_xboole_0)=k2_xboole_0(A_311, k4_xboole_0(A_311, k4_xboole_0(B_312, A_311))))), inference(superposition, [status(thm), theory('equality')], [c_23670, c_2714])).
% 11.48/5.66  tff(c_24002, plain, (![A_313, B_314]: (k4_xboole_0(A_313, k4_xboole_0(B_314, A_313))=A_313)), inference(demodulation, [status(thm), theory('equality')], [c_3373, c_1466, c_23730])).
% 11.48/5.66  tff(c_24299, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1673, c_24002])).
% 11.48/5.66  tff(c_22816, plain, (![C_307, A_308, B_309]: (k3_xboole_0(C_307, k4_xboole_0(A_308, k2_xboole_0(B_309, C_307)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_21860])).
% 11.48/5.66  tff(c_23095, plain, (![A_107, B_108, A_308]: (k3_xboole_0(k4_xboole_0(A_107, B_108), k4_xboole_0(A_308, A_107))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3373, c_22816])).
% 11.48/5.66  tff(c_30674, plain, (![B_108]: (k3_xboole_0(k4_xboole_0('#skF_1', B_108), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24299, c_23095])).
% 11.48/5.66  tff(c_43359, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_43315, c_30674])).
% 11.48/5.66  tff(c_44169, plain, (k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'), k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_43359, c_3010])).
% 11.48/5.66  tff(c_44234, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_12, c_44169])).
% 11.48/5.66  tff(c_24403, plain, (![A_315, B_316]: (r1_xboole_0(A_315, k4_xboole_0(B_316, A_315)))), inference(superposition, [status(thm), theory('equality')], [c_24002, c_18])).
% 11.48/5.66  tff(c_24502, plain, (![C_9, A_7, B_8]: (r1_xboole_0(C_9, k4_xboole_0(A_7, k2_xboole_0(B_8, C_9))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_24403])).
% 11.48/5.66  tff(c_45243, plain, (r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44234, c_24502])).
% 11.48/5.66  tff(c_45439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_45243])).
% 11.48/5.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.48/5.66  
% 11.48/5.66  Inference rules
% 11.48/5.66  ----------------------
% 11.48/5.66  #Ref     : 0
% 11.48/5.66  #Sup     : 11342
% 11.48/5.66  #Fact    : 0
% 11.48/5.66  #Define  : 0
% 11.48/5.66  #Split   : 0
% 11.48/5.66  #Chain   : 0
% 11.48/5.66  #Close   : 0
% 11.48/5.66  
% 11.48/5.66  Ordering : KBO
% 11.48/5.66  
% 11.48/5.66  Simplification rules
% 11.48/5.66  ----------------------
% 11.48/5.66  #Subsume      : 0
% 11.48/5.66  #Demod        : 12247
% 11.48/5.66  #Tautology    : 8284
% 11.48/5.66  #SimpNegUnit  : 1
% 11.48/5.66  #BackRed      : 18
% 11.48/5.66  
% 11.48/5.66  #Partial instantiations: 0
% 11.48/5.66  #Strategies tried      : 1
% 11.48/5.66  
% 11.48/5.66  Timing (in seconds)
% 11.48/5.66  ----------------------
% 11.48/5.66  Preprocessing        : 0.29
% 11.48/5.66  Parsing              : 0.16
% 11.48/5.66  CNF conversion       : 0.02
% 11.48/5.66  Main loop            : 4.52
% 11.48/5.66  Inferencing          : 0.81
% 11.48/5.66  Reduction            : 2.60
% 11.48/5.66  Demodulation         : 2.31
% 11.48/5.66  BG Simplification    : 0.09
% 11.48/5.66  Subsumption          : 0.80
% 11.48/5.66  Abstraction          : 0.16
% 11.48/5.66  MUC search           : 0.00
% 11.48/5.66  Cooper               : 0.00
% 11.48/5.66  Total                : 4.85
% 11.48/5.66  Index Insertion      : 0.00
% 11.48/5.66  Index Deletion       : 0.00
% 11.48/5.66  Index Matching       : 0.00
% 11.48/5.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
