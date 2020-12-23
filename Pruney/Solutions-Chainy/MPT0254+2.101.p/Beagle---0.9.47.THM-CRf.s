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
% DateTime   : Thu Dec  3 09:51:32 EST 2020

% Result     : Theorem 5.23s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  119 (2264 expanded)
%              Number of leaves         :   45 ( 794 expanded)
%              Depth                    :   19
%              Number of atoms          :  105 (2333 expanded)
%              Number of equality atoms :   74 (2131 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_90,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_89,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_529,plain,(
    ! [A_102,B_103] : k5_xboole_0(k5_xboole_0(A_102,B_103),k3_xboole_0(A_102,B_103)) = k2_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3874,plain,(
    ! [A_215,B_216] : k5_xboole_0(k5_xboole_0(A_215,B_216),k3_xboole_0(B_216,A_215)) = k2_xboole_0(A_215,B_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_529])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3913,plain,(
    ! [A_215,B_216] : k5_xboole_0(A_215,k5_xboole_0(B_216,k3_xboole_0(B_216,A_215))) = k2_xboole_0(A_215,B_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_3874,c_24])).

tff(c_4253,plain,(
    ! [A_221,B_222] : k5_xboole_0(A_221,k4_xboole_0(B_222,A_221)) = k2_xboole_0(A_221,B_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3913])).

tff(c_120,plain,(
    ! [B_69,A_70] : k5_xboole_0(B_69,A_70) = k5_xboole_0(A_70,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [A_70] : k5_xboole_0(k1_xboole_0,A_70) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_20])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_657,plain,(
    ! [A_107,B_108,C_109] : k5_xboole_0(k5_xboole_0(A_107,B_108),C_109) = k5_xboole_0(A_107,k5_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_734,plain,(
    ! [A_23,C_109] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_109)) = k5_xboole_0(k1_xboole_0,C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_657])).

tff(c_747,plain,(
    ! [A_23,C_109] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_109)) = C_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_734])).

tff(c_4638,plain,(
    ! [A_227,B_228] : k5_xboole_0(A_227,k2_xboole_0(A_227,B_228)) = k4_xboole_0(B_228,A_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_4253,c_747])).

tff(c_4726,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_4638])).

tff(c_4747,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4726])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_758,plain,(
    ! [A_111,C_112] : k5_xboole_0(A_111,k5_xboole_0(A_111,C_112)) = C_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_734])).

tff(c_810,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k5_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_758])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_299,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1281,plain,(
    ! [A_137,B_138] : k3_xboole_0(k4_xboole_0(A_137,B_138),A_137) = k4_xboole_0(A_137,B_138) ),
    inference(resolution,[status(thm)],[c_18,c_299])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1293,plain,(
    ! [A_137,B_138] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_137,B_138),A_137),k4_xboole_0(A_137,B_138)) = k2_xboole_0(k4_xboole_0(A_137,B_138),A_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_1281,c_28])).

tff(c_1335,plain,(
    ! [A_137,B_138] : k2_xboole_0(k4_xboole_0(A_137,B_138),A_137) = A_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_4,c_4,c_1293])).

tff(c_4796,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4747,c_1335])).

tff(c_4832,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4796,c_62])).

tff(c_1299,plain,(
    ! [A_137,B_138] : k5_xboole_0(k4_xboole_0(A_137,B_138),k4_xboole_0(A_137,B_138)) = k4_xboole_0(k4_xboole_0(A_137,B_138),A_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_1281,c_10])).

tff(c_1336,plain,(
    ! [A_137,B_138] : k4_xboole_0(k4_xboole_0(A_137,B_138),A_137) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1299])).

tff(c_4793,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4747,c_1336])).

tff(c_4910,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4832,c_4793])).

tff(c_855,plain,(
    ! [B_116,A_117] : k5_xboole_0(B_116,k5_xboole_0(A_117,B_116)) = A_117 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_758])).

tff(c_891,plain,(
    ! [A_23,C_109] : k5_xboole_0(k5_xboole_0(A_23,C_109),C_109) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_855])).

tff(c_1518,plain,(
    ! [B_152,B_153] : k3_xboole_0(B_152,k4_xboole_0(B_152,B_153)) = k4_xboole_0(B_152,B_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1281])).

tff(c_1533,plain,(
    ! [B_152,B_153] : k5_xboole_0(k5_xboole_0(B_152,k4_xboole_0(B_152,B_153)),k4_xboole_0(B_152,B_153)) = k2_xboole_0(B_152,k4_xboole_0(B_152,B_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_28])).

tff(c_1565,plain,(
    ! [B_152,B_153] : k2_xboole_0(B_152,k4_xboole_0(B_152,B_153)) = B_152 ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_1533])).

tff(c_4950,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4910,c_1565])).

tff(c_4973,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4796,c_4950])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_366,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_392,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_366])).

tff(c_415,plain,(
    ! [A_94] : k4_xboole_0(A_94,k1_xboole_0) = A_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_392])).

tff(c_427,plain,(
    ! [A_95] : r1_tarski(A_95,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_18])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_431,plain,(
    ! [A_95] : k3_xboole_0(A_95,A_95) = A_95 ),
    inference(resolution,[status(thm)],[c_427,c_12])).

tff(c_586,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_23,A_23)) = k2_xboole_0(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_529])).

tff(c_596,plain,(
    ! [A_23] : k2_xboole_0(A_23,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_431,c_586])).

tff(c_30,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_310,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_319,plain,(
    ! [A_26] : k3_tarski(k1_tarski(A_26)) = k2_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_310])).

tff(c_627,plain,(
    ! [A_26] : k3_tarski(k1_tarski(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_319])).

tff(c_4991,plain,(
    k3_tarski('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4973,c_627])).

tff(c_60,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4868,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4832,c_4832,c_60])).

tff(c_4996,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4991,c_4868])).

tff(c_16,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4866,plain,(
    ! [A_15] : r1_tarski('#skF_5',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4832,c_16])).

tff(c_5004,plain,(
    ! [A_15] : r1_tarski('#skF_4',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4996,c_4866])).

tff(c_22,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_399,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,k3_xboole_0(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_411,plain,(
    ! [A_14,C_92] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_92,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_399])).

tff(c_413,plain,(
    ! [C_92] : ~ r2_hidden(C_92,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_411])).

tff(c_4857,plain,(
    ! [C_92] : ~ r2_hidden(C_92,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4832,c_413])).

tff(c_5005,plain,(
    ! [C_92] : ~ r2_hidden(C_92,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4996,c_4857])).

tff(c_5002,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4996,c_4973])).

tff(c_58,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4863,plain,(
    k1_zfmisc_1('#skF_5') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4832,c_4832,c_58])).

tff(c_5329,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5002,c_4996,c_4996,c_4863])).

tff(c_46,plain,(
    ! [C_58,A_54] :
      ( r2_hidden(C_58,k1_zfmisc_1(A_54))
      | ~ r1_tarski(C_58,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5333,plain,(
    ! [C_58] :
      ( r2_hidden(C_58,'#skF_4')
      | ~ r1_tarski(C_58,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5329,c_46])).

tff(c_5341,plain,(
    ! [C_239] : ~ r1_tarski(C_239,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5005,c_5333])).

tff(c_5360,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_5004,c_5341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.23/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.08  
% 5.23/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 5.23/2.08  
% 5.23/2.08  %Foreground sorts:
% 5.23/2.08  
% 5.23/2.08  
% 5.23/2.08  %Background operators:
% 5.23/2.08  
% 5.23/2.08  
% 5.23/2.08  %Foreground operators:
% 5.23/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.23/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.23/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.23/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.23/2.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.23/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.23/2.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.23/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/2.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.23/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.23/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.23/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.23/2.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.23/2.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.23/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/2.08  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.23/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/2.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.23/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.23/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/2.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.23/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.23/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.23/2.08  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.23/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.23/2.08  
% 5.23/2.10  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.23/2.10  tff(f_94, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.23/2.10  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.23/2.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.23/2.10  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.23/2.10  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.23/2.10  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.23/2.10  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.23/2.10  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.23/2.10  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.23/2.10  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.23/2.10  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.23/2.10  tff(f_88, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.23/2.10  tff(f_90, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 5.23/2.10  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.23/2.10  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.23/2.10  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.23/2.10  tff(f_89, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 5.23/2.10  tff(f_86, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.23/2.10  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.23/2.10  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.23/2.10  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.23/2.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.23/2.10  tff(c_529, plain, (![A_102, B_103]: (k5_xboole_0(k5_xboole_0(A_102, B_103), k3_xboole_0(A_102, B_103))=k2_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.10  tff(c_3874, plain, (![A_215, B_216]: (k5_xboole_0(k5_xboole_0(A_215, B_216), k3_xboole_0(B_216, A_215))=k2_xboole_0(A_215, B_216))), inference(superposition, [status(thm), theory('equality')], [c_2, c_529])).
% 5.23/2.10  tff(c_24, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.23/2.10  tff(c_3913, plain, (![A_215, B_216]: (k5_xboole_0(A_215, k5_xboole_0(B_216, k3_xboole_0(B_216, A_215)))=k2_xboole_0(A_215, B_216))), inference(superposition, [status(thm), theory('equality')], [c_3874, c_24])).
% 5.23/2.10  tff(c_4253, plain, (![A_221, B_222]: (k5_xboole_0(A_221, k4_xboole_0(B_222, A_221))=k2_xboole_0(A_221, B_222))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3913])).
% 5.23/2.10  tff(c_120, plain, (![B_69, A_70]: (k5_xboole_0(B_69, A_70)=k5_xboole_0(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.23/2.10  tff(c_136, plain, (![A_70]: (k5_xboole_0(k1_xboole_0, A_70)=A_70)), inference(superposition, [status(thm), theory('equality')], [c_120, c_20])).
% 5.23/2.10  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.10  tff(c_657, plain, (![A_107, B_108, C_109]: (k5_xboole_0(k5_xboole_0(A_107, B_108), C_109)=k5_xboole_0(A_107, k5_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.23/2.10  tff(c_734, plain, (![A_23, C_109]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_109))=k5_xboole_0(k1_xboole_0, C_109))), inference(superposition, [status(thm), theory('equality')], [c_26, c_657])).
% 5.23/2.10  tff(c_747, plain, (![A_23, C_109]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_109))=C_109)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_734])).
% 5.23/2.10  tff(c_4638, plain, (![A_227, B_228]: (k5_xboole_0(A_227, k2_xboole_0(A_227, B_228))=k4_xboole_0(B_228, A_227))), inference(superposition, [status(thm), theory('equality')], [c_4253, c_747])).
% 5.23/2.10  tff(c_4726, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_4638])).
% 5.23/2.10  tff(c_4747, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4726])).
% 5.23/2.10  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.23/2.10  tff(c_758, plain, (![A_111, C_112]: (k5_xboole_0(A_111, k5_xboole_0(A_111, C_112))=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_734])).
% 5.23/2.10  tff(c_810, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k5_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_758])).
% 5.23/2.10  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.23/2.10  tff(c_299, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.23/2.10  tff(c_1281, plain, (![A_137, B_138]: (k3_xboole_0(k4_xboole_0(A_137, B_138), A_137)=k4_xboole_0(A_137, B_138))), inference(resolution, [status(thm)], [c_18, c_299])).
% 5.23/2.10  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.10  tff(c_1293, plain, (![A_137, B_138]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_137, B_138), A_137), k4_xboole_0(A_137, B_138))=k2_xboole_0(k4_xboole_0(A_137, B_138), A_137))), inference(superposition, [status(thm), theory('equality')], [c_1281, c_28])).
% 5.23/2.10  tff(c_1335, plain, (![A_137, B_138]: (k2_xboole_0(k4_xboole_0(A_137, B_138), A_137)=A_137)), inference(demodulation, [status(thm), theory('equality')], [c_810, c_4, c_4, c_1293])).
% 5.23/2.10  tff(c_4796, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4747, c_1335])).
% 5.23/2.10  tff(c_4832, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4796, c_62])).
% 5.23/2.10  tff(c_1299, plain, (![A_137, B_138]: (k5_xboole_0(k4_xboole_0(A_137, B_138), k4_xboole_0(A_137, B_138))=k4_xboole_0(k4_xboole_0(A_137, B_138), A_137))), inference(superposition, [status(thm), theory('equality')], [c_1281, c_10])).
% 5.23/2.10  tff(c_1336, plain, (![A_137, B_138]: (k4_xboole_0(k4_xboole_0(A_137, B_138), A_137)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1299])).
% 5.23/2.10  tff(c_4793, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4747, c_1336])).
% 5.23/2.10  tff(c_4910, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4832, c_4793])).
% 5.23/2.10  tff(c_855, plain, (![B_116, A_117]: (k5_xboole_0(B_116, k5_xboole_0(A_117, B_116))=A_117)), inference(superposition, [status(thm), theory('equality')], [c_4, c_758])).
% 5.23/2.10  tff(c_891, plain, (![A_23, C_109]: (k5_xboole_0(k5_xboole_0(A_23, C_109), C_109)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_747, c_855])).
% 5.23/2.10  tff(c_1518, plain, (![B_152, B_153]: (k3_xboole_0(B_152, k4_xboole_0(B_152, B_153))=k4_xboole_0(B_152, B_153))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1281])).
% 5.23/2.10  tff(c_1533, plain, (![B_152, B_153]: (k5_xboole_0(k5_xboole_0(B_152, k4_xboole_0(B_152, B_153)), k4_xboole_0(B_152, B_153))=k2_xboole_0(B_152, k4_xboole_0(B_152, B_153)))), inference(superposition, [status(thm), theory('equality')], [c_1518, c_28])).
% 5.23/2.10  tff(c_1565, plain, (![B_152, B_153]: (k2_xboole_0(B_152, k4_xboole_0(B_152, B_153))=B_152)), inference(demodulation, [status(thm), theory('equality')], [c_891, c_1533])).
% 5.23/2.10  tff(c_4950, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4910, c_1565])).
% 5.23/2.10  tff(c_4973, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4796, c_4950])).
% 5.23/2.10  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.23/2.10  tff(c_366, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.23/2.10  tff(c_392, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_366])).
% 5.23/2.10  tff(c_415, plain, (![A_94]: (k4_xboole_0(A_94, k1_xboole_0)=A_94)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_392])).
% 5.23/2.10  tff(c_427, plain, (![A_95]: (r1_tarski(A_95, A_95))), inference(superposition, [status(thm), theory('equality')], [c_415, c_18])).
% 5.23/2.10  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.23/2.10  tff(c_431, plain, (![A_95]: (k3_xboole_0(A_95, A_95)=A_95)), inference(resolution, [status(thm)], [c_427, c_12])).
% 5.23/2.10  tff(c_586, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_23, A_23))=k2_xboole_0(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_26, c_529])).
% 5.23/2.10  tff(c_596, plain, (![A_23]: (k2_xboole_0(A_23, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_431, c_586])).
% 5.23/2.10  tff(c_30, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.23/2.10  tff(c_310, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.23/2.10  tff(c_319, plain, (![A_26]: (k3_tarski(k1_tarski(A_26))=k2_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_30, c_310])).
% 5.23/2.10  tff(c_627, plain, (![A_26]: (k3_tarski(k1_tarski(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_596, c_319])).
% 5.23/2.10  tff(c_4991, plain, (k3_tarski('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4973, c_627])).
% 5.23/2.10  tff(c_60, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.23/2.10  tff(c_4868, plain, (k3_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4832, c_4832, c_60])).
% 5.23/2.10  tff(c_4996, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4991, c_4868])).
% 5.23/2.10  tff(c_16, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.23/2.10  tff(c_4866, plain, (![A_15]: (r1_tarski('#skF_5', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_4832, c_16])).
% 5.23/2.10  tff(c_5004, plain, (![A_15]: (r1_tarski('#skF_4', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_4996, c_4866])).
% 5.23/2.10  tff(c_22, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.23/2.10  tff(c_399, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, k3_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.23/2.10  tff(c_411, plain, (![A_14, C_92]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_399])).
% 5.23/2.10  tff(c_413, plain, (![C_92]: (~r2_hidden(C_92, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_411])).
% 5.23/2.10  tff(c_4857, plain, (![C_92]: (~r2_hidden(C_92, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4832, c_413])).
% 5.23/2.10  tff(c_5005, plain, (![C_92]: (~r2_hidden(C_92, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4996, c_4857])).
% 5.23/2.10  tff(c_5002, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4996, c_4973])).
% 5.23/2.10  tff(c_58, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.23/2.10  tff(c_4863, plain, (k1_zfmisc_1('#skF_5')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4832, c_4832, c_58])).
% 5.23/2.10  tff(c_5329, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5002, c_4996, c_4996, c_4863])).
% 5.23/2.10  tff(c_46, plain, (![C_58, A_54]: (r2_hidden(C_58, k1_zfmisc_1(A_54)) | ~r1_tarski(C_58, A_54))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.23/2.10  tff(c_5333, plain, (![C_58]: (r2_hidden(C_58, '#skF_4') | ~r1_tarski(C_58, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5329, c_46])).
% 5.23/2.10  tff(c_5341, plain, (![C_239]: (~r1_tarski(C_239, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_5005, c_5333])).
% 5.23/2.10  tff(c_5360, plain, $false, inference(resolution, [status(thm)], [c_5004, c_5341])).
% 5.23/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.10  
% 5.23/2.10  Inference rules
% 5.23/2.10  ----------------------
% 5.23/2.10  #Ref     : 0
% 5.23/2.10  #Sup     : 1329
% 5.23/2.10  #Fact    : 0
% 5.23/2.10  #Define  : 0
% 5.23/2.10  #Split   : 0
% 5.23/2.10  #Chain   : 0
% 5.23/2.10  #Close   : 0
% 5.23/2.10  
% 5.23/2.10  Ordering : KBO
% 5.23/2.10  
% 5.23/2.10  Simplification rules
% 5.23/2.10  ----------------------
% 5.23/2.10  #Subsume      : 54
% 5.23/2.10  #Demod        : 1229
% 5.23/2.10  #Tautology    : 806
% 5.23/2.10  #SimpNegUnit  : 7
% 5.23/2.10  #BackRed      : 39
% 5.23/2.10  
% 5.23/2.10  #Partial instantiations: 0
% 5.23/2.10  #Strategies tried      : 1
% 5.23/2.10  
% 5.23/2.10  Timing (in seconds)
% 5.23/2.10  ----------------------
% 5.23/2.10  Preprocessing        : 0.35
% 5.23/2.10  Parsing              : 0.18
% 5.23/2.10  CNF conversion       : 0.02
% 5.23/2.10  Main loop            : 0.93
% 5.23/2.10  Inferencing          : 0.28
% 5.23/2.10  Reduction            : 0.43
% 5.23/2.10  Demodulation         : 0.37
% 5.23/2.10  BG Simplification    : 0.04
% 5.23/2.10  Subsumption          : 0.12
% 5.23/2.10  Abstraction          : 0.05
% 5.23/2.10  MUC search           : 0.00
% 5.23/2.10  Cooper               : 0.00
% 5.23/2.10  Total                : 1.32
% 5.23/2.10  Index Insertion      : 0.00
% 5.23/2.10  Index Deletion       : 0.00
% 5.23/2.10  Index Matching       : 0.00
% 5.23/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
