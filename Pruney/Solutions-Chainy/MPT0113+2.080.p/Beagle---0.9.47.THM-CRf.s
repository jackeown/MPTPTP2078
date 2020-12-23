%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:21 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 238 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  100 ( 302 expanded)
%              Number of equality atoms :   66 ( 186 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_1609,plain,(
    ! [A_100,B_101] :
      ( r1_xboole_0(A_100,B_101)
      | k3_xboole_0(A_100,B_101) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | k4_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_57,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_101,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89,c_57])).

tff(c_24,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_26,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_236,plain,(
    ! [A_54,B_55,C_56] : k3_xboole_0(k3_xboole_0(A_54,B_55),C_56) = k3_xboole_0(A_54,k3_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_256,plain,(
    ! [A_54,B_55,C_56] : k5_xboole_0(k3_xboole_0(A_54,B_55),k3_xboole_0(A_54,k3_xboole_0(B_55,C_56))) = k4_xboole_0(k3_xboole_0(A_54,B_55),C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_10])).

tff(c_1421,plain,(
    ! [A_92,B_93,C_94] : k5_xboole_0(k3_xboole_0(A_92,B_93),k3_xboole_0(A_92,k3_xboole_0(B_93,C_94))) = k3_xboole_0(A_92,k4_xboole_0(B_93,C_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_256])).

tff(c_1518,plain,(
    ! [A_92] : k5_xboole_0(k3_xboole_0(A_92,'#skF_1'),k3_xboole_0(A_92,'#skF_1')) = k3_xboole_0(A_92,k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1421])).

tff(c_1540,plain,(
    ! [A_95] : k3_xboole_0(A_95,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_26,c_1518])).

tff(c_1571,plain,(
    ! [A_95] : k5_xboole_0(A_95,k1_xboole_0) = k4_xboole_0(A_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_10])).

tff(c_1583,plain,(
    ! [A_95] : k4_xboole_0(A_95,k1_xboole_0) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1571])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k4_xboole_0(A_20,B_21),k3_xboole_0(A_20,C_22)) = k4_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_286,plain,(
    ! [A_57,B_58,A_59] :
      ( r1_tarski(A_57,B_58)
      | ~ r1_tarski(A_57,A_59)
      | k4_xboole_0(A_59,B_58) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_337,plain,(
    ! [B_63] :
      ( r1_tarski('#skF_1',B_63)
      | k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),B_63) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_286])).

tff(c_349,plain,(
    ! [B_64] : r1_tarski('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_337])).

tff(c_368,plain,(
    ! [C_65] : r1_tarski('#skF_1',k4_xboole_0('#skF_2',k4_xboole_0('#skF_3',C_65))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_349])).

tff(c_385,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_368])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_432,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_385,c_8])).

tff(c_1595,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_432])).

tff(c_1598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1595])).

tff(c_1599,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1613,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1609,c_1599])).

tff(c_1619,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = k1_xboole_0
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1631,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_1619])).

tff(c_1640,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(A_106,B_107) = A_106
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1652,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_1640])).

tff(c_1816,plain,(
    ! [A_125,B_126,C_127] : k3_xboole_0(k3_xboole_0(A_125,B_126),C_127) = k3_xboole_0(A_125,k3_xboole_0(B_126,C_127)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1833,plain,(
    ! [A_125,B_126,C_127] : k5_xboole_0(k3_xboole_0(A_125,B_126),k3_xboole_0(A_125,k3_xboole_0(B_126,C_127))) = k4_xboole_0(k3_xboole_0(A_125,B_126),C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_1816,c_10])).

tff(c_4169,plain,(
    ! [A_181,B_182,C_183] : k5_xboole_0(k3_xboole_0(A_181,B_182),k3_xboole_0(A_181,k3_xboole_0(B_182,C_183))) = k3_xboole_0(A_181,k4_xboole_0(B_182,C_183)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1833])).

tff(c_4317,plain,(
    ! [A_181] : k5_xboole_0(k3_xboole_0(A_181,'#skF_1'),k3_xboole_0(A_181,'#skF_1')) = k3_xboole_0(A_181,k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1652,c_4169])).

tff(c_4356,plain,(
    ! [A_184] : k3_xboole_0(A_184,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_26,c_4317])).

tff(c_4395,plain,(
    ! [A_184] : k5_xboole_0(A_184,k1_xboole_0) = k4_xboole_0(A_184,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4356,c_10])).

tff(c_4409,plain,(
    ! [A_184] : k4_xboole_0(A_184,k1_xboole_0) = A_184 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4395])).

tff(c_1678,plain,(
    ! [A_110,B_111] :
      ( k3_xboole_0(A_110,B_111) = A_110
      | k4_xboole_0(A_110,B_111) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1640])).

tff(c_1692,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1678])).

tff(c_2197,plain,(
    ! [A_142,B_143,C_144] : k2_xboole_0(k4_xboole_0(A_142,B_143),k3_xboole_0(A_142,C_144)) = k4_xboole_0(A_142,k4_xboole_0(B_143,C_144)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2408,plain,(
    ! [A_149,B_150,C_151] : k4_xboole_0(k4_xboole_0(A_149,B_150),k4_xboole_0(A_149,k4_xboole_0(B_150,C_151))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2197,c_18])).

tff(c_3231,plain,(
    ! [A_166,A_167] : k4_xboole_0(k4_xboole_0(A_166,A_167),k4_xboole_0(A_166,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2408])).

tff(c_3343,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_15,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3231])).

tff(c_4617,plain,(
    ! [A_187] : k4_xboole_0(k1_xboole_0,A_187) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4409,c_3343])).

tff(c_2214,plain,(
    ! [A_142,B_143,C_144] : k4_xboole_0(k4_xboole_0(A_142,B_143),k4_xboole_0(A_142,k4_xboole_0(B_143,C_144))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2197,c_18])).

tff(c_4643,plain,(
    ! [A_142] : k4_xboole_0(k4_xboole_0(A_142,k1_xboole_0),k4_xboole_0(A_142,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4617,c_2214])).

tff(c_5038,plain,(
    ! [A_193] : k4_xboole_0(A_193,A_193) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4409,c_4409,c_4643])).

tff(c_2286,plain,(
    ! [A_15,B_16,C_144] : k4_xboole_0(A_15,k4_xboole_0(k2_xboole_0(A_15,B_16),C_144)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_15,C_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2197])).

tff(c_5062,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_15,k2_xboole_0(A_15,B_16))) = k4_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5038,c_2286])).

tff(c_5149,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4409,c_1692,c_5062])).

tff(c_1600,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1630,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1600,c_1619])).

tff(c_2283,plain,(
    ! [C_144] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_144)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_2197])).

tff(c_7185,plain,(
    ! [C_224] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_224)) = k3_xboole_0('#skF_1',C_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5149,c_2283])).

tff(c_7254,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7185,c_1631])).

tff(c_7325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1613,c_7254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.30  
% 5.90/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.30  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.90/2.30  
% 5.90/2.30  %Foreground sorts:
% 5.90/2.30  
% 5.90/2.30  
% 5.90/2.30  %Background operators:
% 5.90/2.30  
% 5.90/2.30  
% 5.90/2.30  %Foreground operators:
% 5.90/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.90/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.90/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.90/2.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.90/2.30  tff('#skF_2', type, '#skF_2': $i).
% 5.90/2.30  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.30  tff('#skF_1', type, '#skF_1': $i).
% 5.90/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.90/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.90/2.30  
% 6.15/2.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.15/2.32  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.15/2.32  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.15/2.32  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.15/2.32  tff(f_57, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.15/2.32  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.15/2.32  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.15/2.32  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.15/2.32  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.15/2.32  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.15/2.32  tff(f_53, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.15/2.32  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.15/2.32  tff(c_1609, plain, (![A_100, B_101]: (r1_xboole_0(A_100, B_101) | k3_xboole_0(A_100, B_101)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.15/2.32  tff(c_89, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | k4_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.15/2.32  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.15/2.32  tff(c_57, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 6.15/2.32  tff(c_101, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_89, c_57])).
% 6.15/2.32  tff(c_24, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.15/2.32  tff(c_30, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.15/2.32  tff(c_80, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.15/2.32  tff(c_84, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_80])).
% 6.15/2.32  tff(c_26, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.15/2.32  tff(c_66, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.15/2.32  tff(c_70, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_66])).
% 6.15/2.32  tff(c_20, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.15/2.32  tff(c_236, plain, (![A_54, B_55, C_56]: (k3_xboole_0(k3_xboole_0(A_54, B_55), C_56)=k3_xboole_0(A_54, k3_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.15/2.32  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.15/2.32  tff(c_256, plain, (![A_54, B_55, C_56]: (k5_xboole_0(k3_xboole_0(A_54, B_55), k3_xboole_0(A_54, k3_xboole_0(B_55, C_56)))=k4_xboole_0(k3_xboole_0(A_54, B_55), C_56))), inference(superposition, [status(thm), theory('equality')], [c_236, c_10])).
% 6.15/2.32  tff(c_1421, plain, (![A_92, B_93, C_94]: (k5_xboole_0(k3_xboole_0(A_92, B_93), k3_xboole_0(A_92, k3_xboole_0(B_93, C_94)))=k3_xboole_0(A_92, k4_xboole_0(B_93, C_94)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_256])).
% 6.15/2.32  tff(c_1518, plain, (![A_92]: (k5_xboole_0(k3_xboole_0(A_92, '#skF_1'), k3_xboole_0(A_92, '#skF_1'))=k3_xboole_0(A_92, k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1421])).
% 6.15/2.32  tff(c_1540, plain, (![A_95]: (k3_xboole_0(A_95, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_26, c_1518])).
% 6.15/2.32  tff(c_1571, plain, (![A_95]: (k5_xboole_0(A_95, k1_xboole_0)=k4_xboole_0(A_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1540, c_10])).
% 6.15/2.32  tff(c_1583, plain, (![A_95]: (k4_xboole_0(A_95, k1_xboole_0)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1571])).
% 6.15/2.32  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.15/2.32  tff(c_22, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k4_xboole_0(A_20, B_21), k3_xboole_0(A_20, C_22))=k4_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.15/2.32  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.15/2.32  tff(c_115, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.15/2.32  tff(c_286, plain, (![A_57, B_58, A_59]: (r1_tarski(A_57, B_58) | ~r1_tarski(A_57, A_59) | k4_xboole_0(A_59, B_58)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_115])).
% 6.15/2.32  tff(c_337, plain, (![B_63]: (r1_tarski('#skF_1', B_63) | k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), B_63)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_286])).
% 6.15/2.32  tff(c_349, plain, (![B_64]: (r1_tarski('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), B_64)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_337])).
% 6.15/2.32  tff(c_368, plain, (![C_65]: (r1_tarski('#skF_1', k4_xboole_0('#skF_2', k4_xboole_0('#skF_3', C_65))))), inference(superposition, [status(thm), theory('equality')], [c_22, c_349])).
% 6.15/2.32  tff(c_385, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_368])).
% 6.15/2.32  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.15/2.32  tff(c_432, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_385, c_8])).
% 6.15/2.32  tff(c_1595, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_432])).
% 6.15/2.32  tff(c_1598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_1595])).
% 6.15/2.32  tff(c_1599, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 6.15/2.32  tff(c_1613, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1609, c_1599])).
% 6.15/2.32  tff(c_1619, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=k1_xboole_0 | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.15/2.32  tff(c_1631, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_1619])).
% 6.15/2.32  tff(c_1640, plain, (![A_106, B_107]: (k3_xboole_0(A_106, B_107)=A_106 | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.15/2.32  tff(c_1652, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_1640])).
% 6.15/2.32  tff(c_1816, plain, (![A_125, B_126, C_127]: (k3_xboole_0(k3_xboole_0(A_125, B_126), C_127)=k3_xboole_0(A_125, k3_xboole_0(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.15/2.32  tff(c_1833, plain, (![A_125, B_126, C_127]: (k5_xboole_0(k3_xboole_0(A_125, B_126), k3_xboole_0(A_125, k3_xboole_0(B_126, C_127)))=k4_xboole_0(k3_xboole_0(A_125, B_126), C_127))), inference(superposition, [status(thm), theory('equality')], [c_1816, c_10])).
% 6.15/2.32  tff(c_4169, plain, (![A_181, B_182, C_183]: (k5_xboole_0(k3_xboole_0(A_181, B_182), k3_xboole_0(A_181, k3_xboole_0(B_182, C_183)))=k3_xboole_0(A_181, k4_xboole_0(B_182, C_183)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1833])).
% 6.15/2.32  tff(c_4317, plain, (![A_181]: (k5_xboole_0(k3_xboole_0(A_181, '#skF_1'), k3_xboole_0(A_181, '#skF_1'))=k3_xboole_0(A_181, k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1652, c_4169])).
% 6.15/2.32  tff(c_4356, plain, (![A_184]: (k3_xboole_0(A_184, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_26, c_4317])).
% 6.15/2.32  tff(c_4395, plain, (![A_184]: (k5_xboole_0(A_184, k1_xboole_0)=k4_xboole_0(A_184, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4356, c_10])).
% 6.15/2.32  tff(c_4409, plain, (![A_184]: (k4_xboole_0(A_184, k1_xboole_0)=A_184)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4395])).
% 6.15/2.32  tff(c_1678, plain, (![A_110, B_111]: (k3_xboole_0(A_110, B_111)=A_110 | k4_xboole_0(A_110, B_111)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1640])).
% 6.15/2.32  tff(c_1692, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(superposition, [status(thm), theory('equality')], [c_18, c_1678])).
% 6.15/2.32  tff(c_2197, plain, (![A_142, B_143, C_144]: (k2_xboole_0(k4_xboole_0(A_142, B_143), k3_xboole_0(A_142, C_144))=k4_xboole_0(A_142, k4_xboole_0(B_143, C_144)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.15/2.32  tff(c_2408, plain, (![A_149, B_150, C_151]: (k4_xboole_0(k4_xboole_0(A_149, B_150), k4_xboole_0(A_149, k4_xboole_0(B_150, C_151)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2197, c_18])).
% 6.15/2.32  tff(c_3231, plain, (![A_166, A_167]: (k4_xboole_0(k4_xboole_0(A_166, A_167), k4_xboole_0(A_166, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_2408])).
% 6.15/2.32  tff(c_3343, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_15, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_3231])).
% 6.15/2.32  tff(c_4617, plain, (![A_187]: (k4_xboole_0(k1_xboole_0, A_187)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4409, c_3343])).
% 6.15/2.32  tff(c_2214, plain, (![A_142, B_143, C_144]: (k4_xboole_0(k4_xboole_0(A_142, B_143), k4_xboole_0(A_142, k4_xboole_0(B_143, C_144)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2197, c_18])).
% 6.15/2.32  tff(c_4643, plain, (![A_142]: (k4_xboole_0(k4_xboole_0(A_142, k1_xboole_0), k4_xboole_0(A_142, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4617, c_2214])).
% 6.15/2.32  tff(c_5038, plain, (![A_193]: (k4_xboole_0(A_193, A_193)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4409, c_4409, c_4643])).
% 6.15/2.32  tff(c_2286, plain, (![A_15, B_16, C_144]: (k4_xboole_0(A_15, k4_xboole_0(k2_xboole_0(A_15, B_16), C_144))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_15, C_144)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2197])).
% 6.15/2.32  tff(c_5062, plain, (![A_15, B_16]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_15, k2_xboole_0(A_15, B_16)))=k4_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5038, c_2286])).
% 6.15/2.32  tff(c_5149, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_4409, c_1692, c_5062])).
% 6.15/2.32  tff(c_1600, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 6.15/2.32  tff(c_1630, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1600, c_1619])).
% 6.15/2.32  tff(c_2283, plain, (![C_144]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_144))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_144)))), inference(superposition, [status(thm), theory('equality')], [c_1630, c_2197])).
% 6.15/2.32  tff(c_7185, plain, (![C_224]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_224))=k3_xboole_0('#skF_1', C_224))), inference(demodulation, [status(thm), theory('equality')], [c_5149, c_2283])).
% 6.15/2.32  tff(c_7254, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7185, c_1631])).
% 6.15/2.32  tff(c_7325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1613, c_7254])).
% 6.15/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.32  
% 6.15/2.32  Inference rules
% 6.15/2.32  ----------------------
% 6.15/2.32  #Ref     : 0
% 6.15/2.32  #Sup     : 1908
% 6.15/2.32  #Fact    : 0
% 6.15/2.32  #Define  : 0
% 6.15/2.32  #Split   : 4
% 6.15/2.32  #Chain   : 0
% 6.15/2.32  #Close   : 0
% 6.15/2.32  
% 6.15/2.32  Ordering : KBO
% 6.15/2.32  
% 6.15/2.32  Simplification rules
% 6.15/2.32  ----------------------
% 6.15/2.32  #Subsume      : 31
% 6.15/2.32  #Demod        : 1500
% 6.15/2.32  #Tautology    : 1045
% 6.15/2.32  #SimpNegUnit  : 9
% 6.15/2.32  #BackRed      : 19
% 6.15/2.32  
% 6.15/2.32  #Partial instantiations: 0
% 6.15/2.32  #Strategies tried      : 1
% 6.15/2.32  
% 6.15/2.32  Timing (in seconds)
% 6.15/2.32  ----------------------
% 6.15/2.32  Preprocessing        : 0.34
% 6.15/2.32  Parsing              : 0.18
% 6.15/2.32  CNF conversion       : 0.02
% 6.15/2.32  Main loop            : 1.12
% 6.15/2.32  Inferencing          : 0.35
% 6.15/2.32  Reduction            : 0.48
% 6.15/2.32  Demodulation         : 0.38
% 6.15/2.32  BG Simplification    : 0.05
% 6.15/2.32  Subsumption          : 0.17
% 6.15/2.32  Abstraction          : 0.06
% 6.15/2.32  MUC search           : 0.00
% 6.15/2.32  Cooper               : 0.00
% 6.15/2.32  Total                : 1.50
% 6.15/2.32  Index Insertion      : 0.00
% 6.15/2.32  Index Deletion       : 0.00
% 6.15/2.32  Index Matching       : 0.00
% 6.15/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
