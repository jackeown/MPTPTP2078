%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:23 EST 2020

% Result     : Theorem 15.66s
% Output     : CNFRefutation 15.76s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 268 expanded)
%              Number of leaves         :   19 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :   95 ( 318 expanded)
%              Number of equality atoms :   67 ( 225 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_139,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_20])).

tff(c_668,plain,(
    ! [A_54,B_55,C_56] : k4_xboole_0(k3_xboole_0(A_54,B_55),C_56) = k3_xboole_0(A_54,k4_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_65,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_65])).

tff(c_521,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_591,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_521])).

tff(c_605,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_591])).

tff(c_675,plain,(
    ! [A_54,B_55] : k3_xboole_0(A_54,k4_xboole_0(B_55,k3_xboole_0(A_54,B_55))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_605])).

tff(c_606,plain,(
    ! [A_53] : k4_xboole_0(A_53,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_591])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_611,plain,(
    ! [A_53] : k4_xboole_0(A_53,k1_xboole_0) = k3_xboole_0(A_53,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_12])).

tff(c_653,plain,(
    ! [A_53] : k3_xboole_0(A_53,A_53) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_611])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_149,plain,(
    ! [B_34,A_33] :
      ( r1_xboole_0(B_34,A_33)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_139,c_6])).

tff(c_396,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_xboole_0(A_46,k4_xboole_0(B_47,C_48))
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2056,plain,(
    ! [A_96,B_97,C_98] :
      ( k3_xboole_0(A_96,k4_xboole_0(B_97,C_98)) = k1_xboole_0
      | ~ r1_xboole_0(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_396,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_524,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,k4_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_12])).

tff(c_592,plain,(
    ! [A_51,B_52] : k3_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_524])).

tff(c_2248,plain,(
    ! [B_99,C_100] :
      ( k4_xboole_0(B_99,C_100) = k1_xboole_0
      | ~ r1_xboole_0(B_99,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2056,c_592])).

tff(c_2263,plain,(
    ! [A_33,C_100] :
      ( k4_xboole_0(A_33,C_100) = k1_xboole_0
      | k3_xboole_0(A_33,A_33) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_149,c_2248])).

tff(c_2289,plain,(
    ! [A_101,C_102] :
      ( k4_xboole_0(A_101,C_102) = k1_xboole_0
      | k1_xboole_0 != A_101 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_2263])).

tff(c_2504,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(A_103,B_104) = k1_xboole_0
      | k1_xboole_0 != A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_12])).

tff(c_2587,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,k1_xboole_0) = k4_xboole_0(A_103,B_104)
      | k1_xboole_0 != A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2504,c_10])).

tff(c_3376,plain,(
    ! [A_121,B_122] :
      ( k4_xboole_0(A_121,B_122) = A_121
      | k1_xboole_0 != A_121 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2587])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37,plain,(
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [B_14,A_13] : r1_xboole_0(B_14,k4_xboole_0(A_13,B_14)) ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_85,plain,(
    ! [B_14,A_13] : k3_xboole_0(B_14,k4_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_65])).

tff(c_182,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_203,plain,(
    ! [B_14,A_13] : k4_xboole_0(B_14,k4_xboole_0(A_13,B_14)) = k4_xboole_0(B_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_182])).

tff(c_221,plain,(
    ! [B_14,A_13] : k4_xboole_0(B_14,k4_xboole_0(A_13,B_14)) = B_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_203])).

tff(c_4347,plain,(
    ! [B_122] : k4_xboole_0(B_122,k1_xboole_0) = B_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_3376,c_221])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1030,plain,(
    ! [A_66,B_67] : k3_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_524])).

tff(c_32091,plain,(
    ! [A_340,B_341,C_342] : k3_xboole_0(A_340,k4_xboole_0(k4_xboole_0(A_340,B_341),C_342)) = k4_xboole_0(k4_xboole_0(A_340,B_341),C_342) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_14])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_89,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_3136,plain,(
    ! [A_118,B_119,C_120] : k4_xboole_0(k3_xboole_0(A_118,B_119),k3_xboole_0(A_118,k4_xboole_0(B_119,C_120))) = k3_xboole_0(k3_xboole_0(A_118,B_119),C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_12])).

tff(c_3328,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_3136])).

tff(c_3372,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3328])).

tff(c_878,plain,(
    ! [A_59,B_60,C_61] : r1_xboole_0(k3_xboole_0(A_59,k4_xboole_0(B_60,C_61)),C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_16])).

tff(c_1616,plain,(
    ! [A_86,B_87,C_88] : k3_xboole_0(k3_xboole_0(A_86,k4_xboole_0(B_87,C_88)),C_88) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_878,c_2])).

tff(c_13366,plain,(
    ! [A_243,B_244,A_245] : k3_xboole_0(k3_xboole_0(A_243,B_244),k4_xboole_0(A_245,B_244)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_1616])).

tff(c_13592,plain,(
    ! [A_245] : k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0(A_245,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3372,c_13366])).

tff(c_32212,plain,(
    ! [B_341] : k4_xboole_0(k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),B_341),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32091,c_13592])).

tff(c_49242,plain,(
    ! [B_414] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2',B_414),'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_32212])).

tff(c_49587,plain,(
    ! [B_9] : k3_xboole_0('#skF_1',k4_xboole_0(k3_xboole_0('#skF_2',B_9),'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_49242])).

tff(c_53040,plain,(
    ! [B_431] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k4_xboole_0(B_431,'#skF_3'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_49587])).

tff(c_5837,plain,(
    ! [A_148,B_149] : k3_xboole_0(A_148,k4_xboole_0(B_149,k3_xboole_0(A_148,B_149))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_605])).

tff(c_5930,plain,(
    ! [A_148,B_149] : k4_xboole_0(A_148,k4_xboole_0(B_149,k3_xboole_0(A_148,B_149))) = k4_xboole_0(A_148,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5837,c_10])).

tff(c_6072,plain,(
    ! [A_148,B_149] : k4_xboole_0(A_148,k4_xboole_0(B_149,k3_xboole_0(A_148,B_149))) = A_148 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4347,c_5930])).

tff(c_53080,plain,(
    ! [B_431] : k4_xboole_0('#skF_1',k4_xboole_0(k3_xboole_0('#skF_2',k4_xboole_0(B_431,'#skF_3')),k1_xboole_0)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_53040,c_6072])).

tff(c_61582,plain,(
    ! [B_465] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_2',k4_xboole_0(B_465,'#skF_3'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4347,c_14,c_53080])).

tff(c_729,plain,(
    ! [A_54,B_55,B_9] : k3_xboole_0(A_54,k4_xboole_0(B_55,k4_xboole_0(k3_xboole_0(A_54,B_55),B_9))) = k3_xboole_0(k3_xboole_0(A_54,B_55),B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_668])).

tff(c_765,plain,(
    ! [A_54,B_55,B_9] : k3_xboole_0(A_54,k4_xboole_0(B_55,k3_xboole_0(A_54,k4_xboole_0(B_55,B_9)))) = k3_xboole_0(k3_xboole_0(A_54,B_55),B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_729])).

tff(c_61775,plain,(
    k3_xboole_0(k3_xboole_0('#skF_2','#skF_1'),'#skF_3') = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61582,c_765])).

tff(c_702,plain,(
    ! [A_54,B_55,B_7] : k3_xboole_0(A_54,k4_xboole_0(B_55,k3_xboole_0(k3_xboole_0(A_54,B_55),B_7))) = k4_xboole_0(k3_xboole_0(A_54,B_55),B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_10])).

tff(c_762,plain,(
    ! [A_54,B_55,B_7] : k3_xboole_0(A_54,k4_xboole_0(B_55,k3_xboole_0(k3_xboole_0(A_54,B_55),B_7))) = k3_xboole_0(A_54,k4_xboole_0(B_55,B_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_702])).

tff(c_64492,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_1'))) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61775,c_762])).

tff(c_64595,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_64492])).

tff(c_64597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_64595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:31:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.66/8.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.66/8.93  
% 15.66/8.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.66/8.93  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 15.66/8.93  
% 15.66/8.93  %Foreground sorts:
% 15.66/8.93  
% 15.66/8.93  
% 15.66/8.93  %Background operators:
% 15.66/8.93  
% 15.66/8.93  
% 15.66/8.93  %Foreground operators:
% 15.66/8.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.66/8.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.66/8.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.66/8.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.66/8.93  tff('#skF_2', type, '#skF_2': $i).
% 15.66/8.93  tff('#skF_3', type, '#skF_3': $i).
% 15.66/8.93  tff('#skF_1', type, '#skF_1': $i).
% 15.66/8.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.66/8.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.66/8.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.66/8.93  
% 15.76/8.95  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.76/8.95  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 15.76/8.95  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 15.76/8.95  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 15.76/8.95  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 15.76/8.95  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.76/8.95  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 15.76/8.95  tff(f_47, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 15.76/8.95  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 15.76/8.95  tff(c_139, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.76/8.95  tff(c_20, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.76/8.95  tff(c_150, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_20])).
% 15.76/8.95  tff(c_668, plain, (![A_54, B_55, C_56]: (k4_xboole_0(k3_xboole_0(A_54, B_55), C_56)=k3_xboole_0(A_54, k4_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.76/8.95  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.76/8.95  tff(c_32, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.76/8.95  tff(c_35, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_32])).
% 15.76/8.95  tff(c_65, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.76/8.95  tff(c_87, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_65])).
% 15.76/8.95  tff(c_521, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.76/8.95  tff(c_591, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_521])).
% 15.76/8.95  tff(c_605, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_591])).
% 15.76/8.95  tff(c_675, plain, (![A_54, B_55]: (k3_xboole_0(A_54, k4_xboole_0(B_55, k3_xboole_0(A_54, B_55)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_668, c_605])).
% 15.76/8.95  tff(c_606, plain, (![A_53]: (k4_xboole_0(A_53, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_591])).
% 15.76/8.95  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.76/8.95  tff(c_611, plain, (![A_53]: (k4_xboole_0(A_53, k1_xboole_0)=k3_xboole_0(A_53, A_53))), inference(superposition, [status(thm), theory('equality')], [c_606, c_12])).
% 15.76/8.95  tff(c_653, plain, (![A_53]: (k3_xboole_0(A_53, A_53)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_611])).
% 15.76/8.95  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.76/8.95  tff(c_149, plain, (![B_34, A_33]: (r1_xboole_0(B_34, A_33) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_139, c_6])).
% 15.76/8.95  tff(c_396, plain, (![A_46, B_47, C_48]: (r1_xboole_0(A_46, k4_xboole_0(B_47, C_48)) | ~r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.76/8.95  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.76/8.95  tff(c_2056, plain, (![A_96, B_97, C_98]: (k3_xboole_0(A_96, k4_xboole_0(B_97, C_98))=k1_xboole_0 | ~r1_xboole_0(A_96, B_97))), inference(resolution, [status(thm)], [c_396, c_2])).
% 15.76/8.95  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.76/8.95  tff(c_524, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k3_xboole_0(A_51, k4_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_521, c_12])).
% 15.76/8.95  tff(c_592, plain, (![A_51, B_52]: (k3_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_524])).
% 15.76/8.95  tff(c_2248, plain, (![B_99, C_100]: (k4_xboole_0(B_99, C_100)=k1_xboole_0 | ~r1_xboole_0(B_99, B_99))), inference(superposition, [status(thm), theory('equality')], [c_2056, c_592])).
% 15.76/8.95  tff(c_2263, plain, (![A_33, C_100]: (k4_xboole_0(A_33, C_100)=k1_xboole_0 | k3_xboole_0(A_33, A_33)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_149, c_2248])).
% 15.76/8.95  tff(c_2289, plain, (![A_101, C_102]: (k4_xboole_0(A_101, C_102)=k1_xboole_0 | k1_xboole_0!=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_653, c_2263])).
% 15.76/8.95  tff(c_2504, plain, (![A_103, B_104]: (k3_xboole_0(A_103, B_104)=k1_xboole_0 | k1_xboole_0!=A_103)), inference(superposition, [status(thm), theory('equality')], [c_2289, c_12])).
% 15.76/8.95  tff(c_2587, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k1_xboole_0)=k4_xboole_0(A_103, B_104) | k1_xboole_0!=A_103)), inference(superposition, [status(thm), theory('equality')], [c_2504, c_10])).
% 15.76/8.95  tff(c_3376, plain, (![A_121, B_122]: (k4_xboole_0(A_121, B_122)=A_121 | k1_xboole_0!=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2587])).
% 15.76/8.95  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.76/8.95  tff(c_37, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.76/8.95  tff(c_45, plain, (![B_14, A_13]: (r1_xboole_0(B_14, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_16, c_37])).
% 15.76/8.95  tff(c_85, plain, (![B_14, A_13]: (k3_xboole_0(B_14, k4_xboole_0(A_13, B_14))=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_65])).
% 15.76/8.95  tff(c_182, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.76/8.95  tff(c_203, plain, (![B_14, A_13]: (k4_xboole_0(B_14, k4_xboole_0(A_13, B_14))=k4_xboole_0(B_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_85, c_182])).
% 15.76/8.95  tff(c_221, plain, (![B_14, A_13]: (k4_xboole_0(B_14, k4_xboole_0(A_13, B_14))=B_14)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_203])).
% 15.76/8.95  tff(c_4347, plain, (![B_122]: (k4_xboole_0(B_122, k1_xboole_0)=B_122)), inference(superposition, [status(thm), theory('equality')], [c_3376, c_221])).
% 15.76/8.95  tff(c_14, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.76/8.95  tff(c_1030, plain, (![A_66, B_67]: (k3_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_524])).
% 15.76/8.95  tff(c_32091, plain, (![A_340, B_341, C_342]: (k3_xboole_0(A_340, k4_xboole_0(k4_xboole_0(A_340, B_341), C_342))=k4_xboole_0(k4_xboole_0(A_340, B_341), C_342))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_14])).
% 15.76/8.95  tff(c_22, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.76/8.95  tff(c_89, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_65])).
% 15.76/8.95  tff(c_3136, plain, (![A_118, B_119, C_120]: (k4_xboole_0(k3_xboole_0(A_118, B_119), k3_xboole_0(A_118, k4_xboole_0(B_119, C_120)))=k3_xboole_0(k3_xboole_0(A_118, B_119), C_120))), inference(superposition, [status(thm), theory('equality')], [c_668, c_12])).
% 15.76/8.95  tff(c_3328, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_89, c_3136])).
% 15.76/8.95  tff(c_3372, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3328])).
% 15.76/8.95  tff(c_878, plain, (![A_59, B_60, C_61]: (r1_xboole_0(k3_xboole_0(A_59, k4_xboole_0(B_60, C_61)), C_61))), inference(superposition, [status(thm), theory('equality')], [c_668, c_16])).
% 15.76/8.95  tff(c_1616, plain, (![A_86, B_87, C_88]: (k3_xboole_0(k3_xboole_0(A_86, k4_xboole_0(B_87, C_88)), C_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_878, c_2])).
% 15.76/8.95  tff(c_13366, plain, (![A_243, B_244, A_245]: (k3_xboole_0(k3_xboole_0(A_243, B_244), k4_xboole_0(A_245, B_244))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_221, c_1616])).
% 15.76/8.95  tff(c_13592, plain, (![A_245]: (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0(A_245, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3372, c_13366])).
% 15.76/8.95  tff(c_32212, plain, (![B_341]: (k4_xboole_0(k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), B_341), '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32091, c_13592])).
% 15.76/8.95  tff(c_49242, plain, (![B_414]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', B_414), '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_32212])).
% 15.76/8.95  tff(c_49587, plain, (![B_9]: (k3_xboole_0('#skF_1', k4_xboole_0(k3_xboole_0('#skF_2', B_9), '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_49242])).
% 15.76/8.95  tff(c_53040, plain, (![B_431]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k4_xboole_0(B_431, '#skF_3')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_49587])).
% 15.76/8.95  tff(c_5837, plain, (![A_148, B_149]: (k3_xboole_0(A_148, k4_xboole_0(B_149, k3_xboole_0(A_148, B_149)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_668, c_605])).
% 15.76/8.95  tff(c_5930, plain, (![A_148, B_149]: (k4_xboole_0(A_148, k4_xboole_0(B_149, k3_xboole_0(A_148, B_149)))=k4_xboole_0(A_148, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5837, c_10])).
% 15.76/8.95  tff(c_6072, plain, (![A_148, B_149]: (k4_xboole_0(A_148, k4_xboole_0(B_149, k3_xboole_0(A_148, B_149)))=A_148)), inference(demodulation, [status(thm), theory('equality')], [c_4347, c_5930])).
% 15.76/8.95  tff(c_53080, plain, (![B_431]: (k4_xboole_0('#skF_1', k4_xboole_0(k3_xboole_0('#skF_2', k4_xboole_0(B_431, '#skF_3')), k1_xboole_0))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_53040, c_6072])).
% 15.76/8.95  tff(c_61582, plain, (![B_465]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', k4_xboole_0(B_465, '#skF_3')))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4347, c_14, c_53080])).
% 15.76/8.95  tff(c_729, plain, (![A_54, B_55, B_9]: (k3_xboole_0(A_54, k4_xboole_0(B_55, k4_xboole_0(k3_xboole_0(A_54, B_55), B_9)))=k3_xboole_0(k3_xboole_0(A_54, B_55), B_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_668])).
% 15.76/8.95  tff(c_765, plain, (![A_54, B_55, B_9]: (k3_xboole_0(A_54, k4_xboole_0(B_55, k3_xboole_0(A_54, k4_xboole_0(B_55, B_9))))=k3_xboole_0(k3_xboole_0(A_54, B_55), B_9))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_729])).
% 15.76/8.95  tff(c_61775, plain, (k3_xboole_0(k3_xboole_0('#skF_2', '#skF_1'), '#skF_3')=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61582, c_765])).
% 15.76/8.95  tff(c_702, plain, (![A_54, B_55, B_7]: (k3_xboole_0(A_54, k4_xboole_0(B_55, k3_xboole_0(k3_xboole_0(A_54, B_55), B_7)))=k4_xboole_0(k3_xboole_0(A_54, B_55), B_7))), inference(superposition, [status(thm), theory('equality')], [c_668, c_10])).
% 15.76/8.95  tff(c_762, plain, (![A_54, B_55, B_7]: (k3_xboole_0(A_54, k4_xboole_0(B_55, k3_xboole_0(k3_xboole_0(A_54, B_55), B_7)))=k3_xboole_0(A_54, k4_xboole_0(B_55, B_7)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_702])).
% 15.76/8.95  tff(c_64492, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_1')))=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_61775, c_762])).
% 15.76/8.95  tff(c_64595, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_675, c_64492])).
% 15.76/8.95  tff(c_64597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_64595])).
% 15.76/8.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.76/8.95  
% 15.76/8.95  Inference rules
% 15.76/8.95  ----------------------
% 15.76/8.95  #Ref     : 0
% 15.76/8.95  #Sup     : 16293
% 15.76/8.95  #Fact    : 0
% 15.76/8.95  #Define  : 0
% 15.76/8.95  #Split   : 1
% 15.76/8.95  #Chain   : 0
% 15.76/8.95  #Close   : 0
% 15.76/8.95  
% 15.76/8.95  Ordering : KBO
% 15.76/8.95  
% 15.76/8.95  Simplification rules
% 15.76/8.95  ----------------------
% 15.76/8.95  #Subsume      : 2963
% 15.76/8.95  #Demod        : 13821
% 15.76/8.95  #Tautology    : 9704
% 15.76/8.95  #SimpNegUnit  : 141
% 15.76/8.95  #BackRed      : 1
% 15.76/8.95  
% 15.76/8.95  #Partial instantiations: 0
% 15.76/8.95  #Strategies tried      : 1
% 15.76/8.95  
% 15.76/8.95  Timing (in seconds)
% 15.76/8.95  ----------------------
% 15.76/8.95  Preprocessing        : 0.28
% 15.76/8.95  Parsing              : 0.15
% 15.76/8.95  CNF conversion       : 0.02
% 15.76/8.95  Main loop            : 7.89
% 15.76/8.95  Inferencing          : 1.13
% 15.76/8.95  Reduction            : 4.97
% 15.76/8.95  Demodulation         : 4.46
% 15.76/8.95  BG Simplification    : 0.12
% 15.76/8.95  Subsumption          : 1.39
% 15.76/8.95  Abstraction          : 0.22
% 15.76/8.95  MUC search           : 0.00
% 15.76/8.95  Cooper               : 0.00
% 15.76/8.95  Total                : 8.21
% 15.76/8.95  Index Insertion      : 0.00
% 15.76/8.95  Index Deletion       : 0.00
% 15.76/8.95  Index Matching       : 0.00
% 15.76/8.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
