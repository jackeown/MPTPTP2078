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
% DateTime   : Thu Dec  3 09:43:40 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 216 expanded)
%              Number of leaves         :   21 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :   80 ( 224 expanded)
%              Number of equality atoms :   73 ( 207 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_22,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_190])).

tff(c_212,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_208])).

tff(c_348,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k4_xboole_0(A_36,B_37),C_38) = k4_xboole_0(A_36,k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1627,plain,(
    ! [C_66,A_67,B_68] : k2_xboole_0(C_66,k4_xboole_0(A_67,k2_xboole_0(B_68,C_66))) = k2_xboole_0(C_66,k4_xboole_0(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_12])).

tff(c_1714,plain,(
    ! [C_66,B_68] : k2_xboole_0(C_66,k4_xboole_0(k2_xboole_0(B_68,C_66),B_68)) = k2_xboole_0(C_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_1627])).

tff(c_1942,plain,(
    ! [C_70,B_71] : k2_xboole_0(C_70,k4_xboole_0(k2_xboole_0(B_71,C_70),B_71)) = C_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1714])).

tff(c_2044,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(k2_xboole_0(A_1,B_2),B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1942])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_145,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_145])).

tff(c_238,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_256,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_238])).

tff(c_54,plain,(
    ! [B_20,A_21] : k2_xboole_0(B_20,A_21) = k2_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_21] : k2_xboole_0(k1_xboole_0,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_420,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_70])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_432,plain,(
    ! [C_12] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_12)) = k4_xboole_0('#skF_3',C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_16])).

tff(c_28,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_361,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(B_37,k4_xboole_0(A_36,B_37))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_212])).

tff(c_497,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k2_xboole_0(B_41,A_40)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_361])).

tff(c_733,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_497])).

tff(c_787,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_733])).

tff(c_1684,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_1627])).

tff(c_1749,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1684])).

tff(c_20,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(A_15,B_16),k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_351,plain,(
    ! [A_36,B_37,C_38,C_12] : k4_xboole_0(k4_xboole_0(A_36,k2_xboole_0(B_37,C_38)),C_12) = k4_xboole_0(k4_xboole_0(A_36,B_37),k2_xboole_0(C_38,C_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_16])).

tff(c_5690,plain,(
    ! [A_115,B_116,C_117,C_118] : k4_xboole_0(A_115,k2_xboole_0(k2_xboole_0(B_116,C_117),C_118)) = k4_xboole_0(A_115,k2_xboole_0(B_116,k2_xboole_0(C_117,C_118))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_351])).

tff(c_408,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(B_37,A_36)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_361])).

tff(c_6041,plain,(
    ! [C_119,B_120,C_121] : k4_xboole_0(C_119,k2_xboole_0(B_120,k2_xboole_0(C_121,C_119))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5690,c_408])).

tff(c_8308,plain,(
    ! [A_138,B_139,B_140] : k4_xboole_0(k4_xboole_0(A_138,B_139),k2_xboole_0(B_140,A_138)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6041])).

tff(c_8508,plain,(
    ! [B_139] : k4_xboole_0(k4_xboole_0(k4_xboole_0('#skF_3','#skF_1'),B_139),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_8308])).

tff(c_8688,plain,(
    ! [B_141] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_1',B_141)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_2,c_16,c_16,c_8508])).

tff(c_8785,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_8688])).

tff(c_9103,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8785,c_12])).

tff(c_9122,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9103])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_153,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_145])).

tff(c_253,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_238])).

tff(c_322,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_70])).

tff(c_384,plain,(
    ! [C_38] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_38)) = k4_xboole_0('#skF_1',C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_348])).

tff(c_371,plain,(
    ! [C_38,A_36,B_37] : k2_xboole_0(C_38,k4_xboole_0(A_36,k2_xboole_0(B_37,C_38))) = k2_xboole_0(C_38,k4_xboole_0(A_36,B_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_12])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_398,plain,(
    ! [A_36,B_37,B_14] : k4_xboole_0(A_36,k2_xboole_0(B_37,k4_xboole_0(k4_xboole_0(A_36,B_37),B_14))) = k3_xboole_0(k4_xboole_0(A_36,B_37),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_348])).

tff(c_4273,plain,(
    ! [A_99,B_100,B_101] : k4_xboole_0(A_99,k2_xboole_0(B_100,k4_xboole_0(A_99,k2_xboole_0(B_100,B_101)))) = k3_xboole_0(k4_xboole_0(A_99,B_100),B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_398])).

tff(c_4433,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(B_37,k4_xboole_0(A_36,B_37))) = k3_xboole_0(k4_xboole_0(A_36,B_37),B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_4273])).

tff(c_4577,plain,(
    ! [A_102,B_103] : k3_xboole_0(k4_xboole_0(A_102,B_103),B_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_12,c_4433])).

tff(c_4725,plain,(
    ! [A_104,B_105,C_106] : k3_xboole_0(k4_xboole_0(A_104,k2_xboole_0(B_105,C_106)),C_106) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4577])).

tff(c_15061,plain,(
    ! [A_181,A_182,B_183] : k3_xboole_0(k4_xboole_0(A_181,k2_xboole_0(A_182,B_183)),A_182) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4725])).

tff(c_15203,plain,(
    ! [C_38] : k3_xboole_0(k4_xboole_0('#skF_1',C_38),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_15061])).

tff(c_550,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_497])).

tff(c_9738,plain,(
    ! [A_146,B_147,C_148] : k4_xboole_0(k4_xboole_0(A_146,B_147),k4_xboole_0(A_146,k2_xboole_0(B_147,C_148))) = k3_xboole_0(k4_xboole_0(A_146,B_147),C_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_18])).

tff(c_10260,plain,(
    ! [A_150] : k4_xboole_0(k4_xboole_0(A_150,'#skF_3'),k4_xboole_0(A_150,k2_xboole_0('#skF_1','#skF_2'))) = k3_xboole_0(k4_xboole_0(A_150,'#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9738])).

tff(c_10379,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k1_xboole_0) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_10260])).

tff(c_10436,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10379])).

tff(c_15402,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15203,c_10436])).

tff(c_15637,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15402,c_12])).

tff(c_15660,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9122,c_2,c_8,c_15637])).

tff(c_15662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_15660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:37:51 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.80/3.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/3.02  
% 7.80/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/3.03  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.80/3.03  
% 7.80/3.03  %Foreground sorts:
% 7.80/3.03  
% 7.80/3.03  
% 7.80/3.03  %Background operators:
% 7.80/3.03  
% 7.80/3.03  
% 7.80/3.03  %Foreground operators:
% 7.80/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.80/3.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.80/3.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.80/3.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.80/3.03  tff('#skF_2', type, '#skF_2': $i).
% 7.80/3.03  tff('#skF_3', type, '#skF_3': $i).
% 7.80/3.03  tff('#skF_1', type, '#skF_1': $i).
% 7.80/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.80/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.80/3.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.80/3.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.80/3.03  
% 7.80/3.04  tff(f_54, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 7.80/3.04  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.80/3.04  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.80/3.04  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.80/3.04  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.80/3.04  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.80/3.04  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.80/3.04  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.80/3.04  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.80/3.04  tff(f_45, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 7.80/3.04  tff(c_22, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.80/3.04  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.80/3.04  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.80/3.04  tff(c_10, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.80/3.04  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.80/3.04  tff(c_190, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.80/3.04  tff(c_208, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_190])).
% 7.80/3.04  tff(c_212, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_208])).
% 7.80/3.04  tff(c_348, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k4_xboole_0(A_36, B_37), C_38)=k4_xboole_0(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.80/3.04  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.80/3.04  tff(c_1627, plain, (![C_66, A_67, B_68]: (k2_xboole_0(C_66, k4_xboole_0(A_67, k2_xboole_0(B_68, C_66)))=k2_xboole_0(C_66, k4_xboole_0(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_348, c_12])).
% 7.80/3.04  tff(c_1714, plain, (![C_66, B_68]: (k2_xboole_0(C_66, k4_xboole_0(k2_xboole_0(B_68, C_66), B_68))=k2_xboole_0(C_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_212, c_1627])).
% 7.80/3.04  tff(c_1942, plain, (![C_70, B_71]: (k2_xboole_0(C_70, k4_xboole_0(k2_xboole_0(B_71, C_70), B_71))=C_70)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1714])).
% 7.80/3.04  tff(c_2044, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(k2_xboole_0(A_1, B_2), B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1942])).
% 7.80/3.04  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.80/3.04  tff(c_145, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.80/3.04  tff(c_152, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_145])).
% 7.80/3.04  tff(c_238, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/3.04  tff(c_256, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_152, c_238])).
% 7.80/3.04  tff(c_54, plain, (![B_20, A_21]: (k2_xboole_0(B_20, A_21)=k2_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.80/3.04  tff(c_70, plain, (![A_21]: (k2_xboole_0(k1_xboole_0, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 7.80/3.04  tff(c_420, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_256, c_70])).
% 7.80/3.04  tff(c_16, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.80/3.04  tff(c_432, plain, (![C_12]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_12))=k4_xboole_0('#skF_3', C_12))), inference(superposition, [status(thm), theory('equality')], [c_420, c_16])).
% 7.80/3.04  tff(c_28, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.80/3.04  tff(c_361, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(B_37, k4_xboole_0(A_36, B_37)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_348, c_212])).
% 7.80/3.04  tff(c_497, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k2_xboole_0(B_41, A_40))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_361])).
% 7.80/3.04  tff(c_733, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(A_46, B_47))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_497])).
% 7.80/3.04  tff(c_787, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_28, c_733])).
% 7.80/3.04  tff(c_1684, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_787, c_1627])).
% 7.80/3.04  tff(c_1749, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1684])).
% 7.80/3.04  tff(c_20, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(A_15, B_16), k4_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/3.04  tff(c_351, plain, (![A_36, B_37, C_38, C_12]: (k4_xboole_0(k4_xboole_0(A_36, k2_xboole_0(B_37, C_38)), C_12)=k4_xboole_0(k4_xboole_0(A_36, B_37), k2_xboole_0(C_38, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_348, c_16])).
% 7.80/3.04  tff(c_5690, plain, (![A_115, B_116, C_117, C_118]: (k4_xboole_0(A_115, k2_xboole_0(k2_xboole_0(B_116, C_117), C_118))=k4_xboole_0(A_115, k2_xboole_0(B_116, k2_xboole_0(C_117, C_118))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_351])).
% 7.80/3.04  tff(c_408, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(B_37, A_36))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_361])).
% 7.80/3.04  tff(c_6041, plain, (![C_119, B_120, C_121]: (k4_xboole_0(C_119, k2_xboole_0(B_120, k2_xboole_0(C_121, C_119)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5690, c_408])).
% 7.80/3.04  tff(c_8308, plain, (![A_138, B_139, B_140]: (k4_xboole_0(k4_xboole_0(A_138, B_139), k2_xboole_0(B_140, A_138))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_6041])).
% 7.80/3.04  tff(c_8508, plain, (![B_139]: (k4_xboole_0(k4_xboole_0(k4_xboole_0('#skF_3', '#skF_1'), B_139), '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1749, c_8308])).
% 7.80/3.04  tff(c_8688, plain, (![B_141]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', B_141))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_432, c_2, c_16, c_16, c_8508])).
% 7.80/3.04  tff(c_8785, plain, (k4_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2044, c_8688])).
% 7.80/3.04  tff(c_9103, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8785, c_12])).
% 7.80/3.04  tff(c_9122, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_9103])).
% 7.80/3.04  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.80/3.04  tff(c_153, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_145])).
% 7.80/3.04  tff(c_253, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_153, c_238])).
% 7.80/3.04  tff(c_322, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_253, c_70])).
% 7.80/3.04  tff(c_384, plain, (![C_38]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_38))=k4_xboole_0('#skF_1', C_38))), inference(superposition, [status(thm), theory('equality')], [c_322, c_348])).
% 7.80/3.04  tff(c_371, plain, (![C_38, A_36, B_37]: (k2_xboole_0(C_38, k4_xboole_0(A_36, k2_xboole_0(B_37, C_38)))=k2_xboole_0(C_38, k4_xboole_0(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_348, c_12])).
% 7.80/3.04  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.80/3.04  tff(c_398, plain, (![A_36, B_37, B_14]: (k4_xboole_0(A_36, k2_xboole_0(B_37, k4_xboole_0(k4_xboole_0(A_36, B_37), B_14)))=k3_xboole_0(k4_xboole_0(A_36, B_37), B_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_348])).
% 7.80/3.04  tff(c_4273, plain, (![A_99, B_100, B_101]: (k4_xboole_0(A_99, k2_xboole_0(B_100, k4_xboole_0(A_99, k2_xboole_0(B_100, B_101))))=k3_xboole_0(k4_xboole_0(A_99, B_100), B_101))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_398])).
% 7.80/3.04  tff(c_4433, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(B_37, k4_xboole_0(A_36, B_37)))=k3_xboole_0(k4_xboole_0(A_36, B_37), B_37))), inference(superposition, [status(thm), theory('equality')], [c_371, c_4273])).
% 7.80/3.04  tff(c_4577, plain, (![A_102, B_103]: (k3_xboole_0(k4_xboole_0(A_102, B_103), B_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_408, c_12, c_4433])).
% 7.80/3.04  tff(c_4725, plain, (![A_104, B_105, C_106]: (k3_xboole_0(k4_xboole_0(A_104, k2_xboole_0(B_105, C_106)), C_106)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_4577])).
% 7.80/3.04  tff(c_15061, plain, (![A_181, A_182, B_183]: (k3_xboole_0(k4_xboole_0(A_181, k2_xboole_0(A_182, B_183)), A_182)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4725])).
% 7.80/3.04  tff(c_15203, plain, (![C_38]: (k3_xboole_0(k4_xboole_0('#skF_1', C_38), '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_384, c_15061])).
% 7.80/3.04  tff(c_550, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_497])).
% 7.80/3.04  tff(c_9738, plain, (![A_146, B_147, C_148]: (k4_xboole_0(k4_xboole_0(A_146, B_147), k4_xboole_0(A_146, k2_xboole_0(B_147, C_148)))=k3_xboole_0(k4_xboole_0(A_146, B_147), C_148))), inference(superposition, [status(thm), theory('equality')], [c_348, c_18])).
% 7.80/3.04  tff(c_10260, plain, (![A_150]: (k4_xboole_0(k4_xboole_0(A_150, '#skF_3'), k4_xboole_0(A_150, k2_xboole_0('#skF_1', '#skF_2')))=k3_xboole_0(k4_xboole_0(A_150, '#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_9738])).
% 7.80/3.04  tff(c_10379, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_550, c_10260])).
% 7.80/3.04  tff(c_10436, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10379])).
% 7.80/3.04  tff(c_15402, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15203, c_10436])).
% 7.80/3.04  tff(c_15637, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15402, c_12])).
% 7.80/3.04  tff(c_15660, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9122, c_2, c_8, c_15637])).
% 7.80/3.04  tff(c_15662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_15660])).
% 7.80/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/3.04  
% 7.80/3.04  Inference rules
% 7.80/3.04  ----------------------
% 7.80/3.04  #Ref     : 0
% 7.80/3.04  #Sup     : 3952
% 7.80/3.04  #Fact    : 0
% 7.80/3.04  #Define  : 0
% 7.80/3.04  #Split   : 0
% 7.80/3.04  #Chain   : 0
% 7.80/3.04  #Close   : 0
% 7.80/3.04  
% 7.80/3.04  Ordering : KBO
% 7.80/3.04  
% 7.80/3.04  Simplification rules
% 7.80/3.04  ----------------------
% 7.80/3.04  #Subsume      : 3
% 7.80/3.04  #Demod        : 4655
% 7.80/3.04  #Tautology    : 2703
% 7.80/3.04  #SimpNegUnit  : 1
% 7.80/3.04  #BackRed      : 9
% 7.80/3.04  
% 7.80/3.04  #Partial instantiations: 0
% 7.80/3.04  #Strategies tried      : 1
% 7.80/3.04  
% 7.80/3.04  Timing (in seconds)
% 7.80/3.04  ----------------------
% 7.80/3.05  Preprocessing        : 0.27
% 7.80/3.05  Parsing              : 0.14
% 7.80/3.05  CNF conversion       : 0.01
% 7.80/3.05  Main loop            : 2.00
% 7.80/3.05  Inferencing          : 0.45
% 7.80/3.05  Reduction            : 1.13
% 7.80/3.05  Demodulation         : 0.99
% 7.80/3.05  BG Simplification    : 0.05
% 7.80/3.05  Subsumption          : 0.27
% 7.80/3.05  Abstraction          : 0.09
% 7.80/3.05  MUC search           : 0.00
% 7.80/3.05  Cooper               : 0.00
% 7.80/3.05  Total                : 2.31
% 7.80/3.05  Index Insertion      : 0.00
% 7.80/3.05  Index Deletion       : 0.00
% 7.80/3.05  Index Matching       : 0.00
% 7.80/3.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
