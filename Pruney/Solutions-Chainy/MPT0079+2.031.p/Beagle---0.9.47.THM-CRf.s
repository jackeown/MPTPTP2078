%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:46 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 238 expanded)
%              Number of leaves         :   28 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 280 expanded)
%              Number of equality atoms :   73 ( 212 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_38,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_360,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_371,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_360])).

tff(c_686,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_714,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_686])).

tff(c_730,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_714])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_829,plain,(
    ! [A_74,B_75] : k2_xboole_0(k3_xboole_0(A_74,B_75),k4_xboole_0(A_74,B_75)) = A_74 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    ! [B_39,A_40] : r1_tarski(B_39,k2_xboole_0(A_40,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_36])).

tff(c_989,plain,(
    ! [A_78,B_79] : r1_tarski(k4_xboole_0(A_78,B_79),A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_101])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1032,plain,(
    ! [A_78,B_79] : k4_xboole_0(k4_xboole_0(A_78,B_79),A_78) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_989,c_10])).

tff(c_1290,plain,(
    ! [A_86,B_87] : k2_xboole_0(A_86,k4_xboole_0(B_87,A_86)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1327,plain,(
    ! [A_78,B_79] : k2_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k2_xboole_0(A_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_1290])).

tff(c_1381,plain,(
    ! [A_78,B_79] : k2_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1327])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_372,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_360])).

tff(c_3249,plain,(
    ! [A_135,B_136,C_137] : k2_xboole_0(k4_xboole_0(A_135,B_136),k3_xboole_0(A_135,C_137)) = k4_xboole_0(A_135,k4_xboole_0(B_136,C_137)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3363,plain,(
    ! [B_136] : k4_xboole_0('#skF_3',k4_xboole_0(B_136,'#skF_1')) = k2_xboole_0(k4_xboole_0('#skF_3',B_136),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_3249])).

tff(c_3416,plain,(
    ! [B_136] : k4_xboole_0('#skF_3',k4_xboole_0(B_136,'#skF_1')) = k4_xboole_0('#skF_3',B_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3363])).

tff(c_202,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_222,plain,(
    ! [B_39,A_40] : k4_xboole_0(B_39,k2_xboole_0(A_40,B_39)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_202])).

tff(c_44,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_45,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_491,plain,(
    ! [A_62,B_63] : k4_xboole_0(k2_xboole_0(A_62,B_63),B_63) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1857,plain,(
    ! [A_96,B_97] : k4_xboole_0(k2_xboole_0(A_96,B_97),A_96) = k4_xboole_0(B_97,A_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_491])).

tff(c_1932,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_1857])).

tff(c_7168,plain,(
    ! [B_175] : k4_xboole_0('#skF_3',k4_xboole_0(B_175,'#skF_1')) = k4_xboole_0('#skF_3',B_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3363])).

tff(c_7242,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_1')) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1932,c_7168])).

tff(c_7302,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3416,c_222,c_7242])).

tff(c_26,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7366,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7302,c_26])).

tff(c_7386,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7366])).

tff(c_32,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k4_xboole_0(A_26,B_27),k3_xboole_0(A_26,C_28)) = k4_xboole_0(A_26,k4_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7468,plain,(
    ! [B_27] : k4_xboole_0('#skF_3',k4_xboole_0(B_27,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_3',B_27),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7386,c_32])).

tff(c_8061,plain,(
    ! [B_185] : k4_xboole_0('#skF_3',k4_xboole_0(B_185,'#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_2,c_7468])).

tff(c_8152,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_8061])).

tff(c_71,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_225,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_202])).

tff(c_535,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_576,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = k3_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_535])).

tff(c_587,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_576])).

tff(c_3351,plain,(
    ! [A_7,B_136] : k4_xboole_0(A_7,k4_xboole_0(B_136,A_7)) = k2_xboole_0(k4_xboole_0(A_7,B_136),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_3249])).

tff(c_3582,plain,(
    ! [A_140,B_141] : k4_xboole_0(A_140,k4_xboole_0(B_141,A_140)) = A_140 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_2,c_3351])).

tff(c_3696,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_3582])).

tff(c_516,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_491])).

tff(c_16,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7354,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7302,c_16])).

tff(c_7383,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_7354])).

tff(c_381,plain,(
    ! [A_59,B_60] : k2_xboole_0(A_59,k2_xboole_0(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4101,plain,(
    ! [B_144,A_145] : k2_xboole_0(B_144,k2_xboole_0(A_145,B_144)) = k2_xboole_0(B_144,A_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_381])).

tff(c_4238,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_4101])).

tff(c_4276,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_2,c_4238])).

tff(c_1961,plain,(
    ! [A_98,B_99,C_100] : k2_xboole_0(k2_xboole_0(A_98,B_99),C_100) = k2_xboole_0(A_98,k2_xboole_0(B_99,C_100)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8199,plain,(
    ! [C_186,A_187,B_188] : k2_xboole_0(C_186,k2_xboole_0(A_187,B_188)) = k2_xboole_0(A_187,k2_xboole_0(B_188,C_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1961,c_2])).

tff(c_8496,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4276,c_8199])).

tff(c_8688,plain,(
    k2_xboole_0('#skF_4','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7383,c_8496])).

tff(c_9095,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8688,c_516])).

tff(c_9132,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8152,c_3696,c_516,c_9095])).

tff(c_9134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_9132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.67/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.44  
% 6.77/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.44  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.77/2.44  
% 6.77/2.44  %Foreground sorts:
% 6.77/2.44  
% 6.77/2.44  
% 6.77/2.44  %Background operators:
% 6.77/2.44  
% 6.77/2.44  
% 6.77/2.44  %Foreground operators:
% 6.77/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.77/2.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.77/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.77/2.44  tff('#skF_2', type, '#skF_2': $i).
% 6.77/2.44  tff('#skF_3', type, '#skF_3': $i).
% 6.77/2.44  tff('#skF_1', type, '#skF_1': $i).
% 6.77/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.44  tff('#skF_4', type, '#skF_4': $i).
% 6.77/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.77/2.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.77/2.44  
% 6.77/2.46  tff(f_70, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 6.77/2.46  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.77/2.46  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.77/2.46  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.77/2.46  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.77/2.46  tff(f_55, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.77/2.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.77/2.46  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.77/2.46  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.77/2.46  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.77/2.46  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.77/2.46  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.77/2.46  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.77/2.46  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 6.77/2.46  tff(f_53, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.77/2.46  tff(c_38, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.77/2.46  tff(c_18, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.77/2.46  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.77/2.46  tff(c_360, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.46  tff(c_371, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_360])).
% 6.77/2.46  tff(c_686, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.77/2.46  tff(c_714, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_371, c_686])).
% 6.77/2.46  tff(c_730, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_714])).
% 6.77/2.46  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.77/2.46  tff(c_829, plain, (![A_74, B_75]: (k2_xboole_0(k3_xboole_0(A_74, B_75), k4_xboole_0(A_74, B_75))=A_74)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.77/2.46  tff(c_83, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.77/2.46  tff(c_36, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.77/2.46  tff(c_101, plain, (![B_39, A_40]: (r1_tarski(B_39, k2_xboole_0(A_40, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_36])).
% 6.77/2.46  tff(c_989, plain, (![A_78, B_79]: (r1_tarski(k4_xboole_0(A_78, B_79), A_78))), inference(superposition, [status(thm), theory('equality')], [c_829, c_101])).
% 6.77/2.46  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.77/2.46  tff(c_1032, plain, (![A_78, B_79]: (k4_xboole_0(k4_xboole_0(A_78, B_79), A_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_989, c_10])).
% 6.77/2.46  tff(c_1290, plain, (![A_86, B_87]: (k2_xboole_0(A_86, k4_xboole_0(B_87, A_86))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.46  tff(c_1327, plain, (![A_78, B_79]: (k2_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k2_xboole_0(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_1290])).
% 6.77/2.46  tff(c_1381, plain, (![A_78, B_79]: (k2_xboole_0(A_78, k4_xboole_0(A_78, B_79))=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1327])).
% 6.77/2.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.77/2.46  tff(c_42, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.77/2.46  tff(c_372, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_360])).
% 6.77/2.46  tff(c_3249, plain, (![A_135, B_136, C_137]: (k2_xboole_0(k4_xboole_0(A_135, B_136), k3_xboole_0(A_135, C_137))=k4_xboole_0(A_135, k4_xboole_0(B_136, C_137)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.77/2.46  tff(c_3363, plain, (![B_136]: (k4_xboole_0('#skF_3', k4_xboole_0(B_136, '#skF_1'))=k2_xboole_0(k4_xboole_0('#skF_3', B_136), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_372, c_3249])).
% 6.77/2.46  tff(c_3416, plain, (![B_136]: (k4_xboole_0('#skF_3', k4_xboole_0(B_136, '#skF_1'))=k4_xboole_0('#skF_3', B_136))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3363])).
% 6.77/2.46  tff(c_202, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.77/2.46  tff(c_222, plain, (![B_39, A_40]: (k4_xboole_0(B_39, k2_xboole_0(A_40, B_39))=k1_xboole_0)), inference(resolution, [status(thm)], [c_101, c_202])).
% 6.77/2.46  tff(c_44, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.77/2.46  tff(c_45, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 6.77/2.46  tff(c_491, plain, (![A_62, B_63]: (k4_xboole_0(k2_xboole_0(A_62, B_63), B_63)=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.77/2.46  tff(c_1857, plain, (![A_96, B_97]: (k4_xboole_0(k2_xboole_0(A_96, B_97), A_96)=k4_xboole_0(B_97, A_96))), inference(superposition, [status(thm), theory('equality')], [c_2, c_491])).
% 6.77/2.46  tff(c_1932, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45, c_1857])).
% 6.77/2.46  tff(c_7168, plain, (![B_175]: (k4_xboole_0('#skF_3', k4_xboole_0(B_175, '#skF_1'))=k4_xboole_0('#skF_3', B_175))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3363])).
% 6.77/2.46  tff(c_7242, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_1'))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1932, c_7168])).
% 6.77/2.46  tff(c_7302, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3416, c_222, c_7242])).
% 6.77/2.46  tff(c_26, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.46  tff(c_7366, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7302, c_26])).
% 6.77/2.46  tff(c_7386, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7366])).
% 6.77/2.46  tff(c_32, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k4_xboole_0(A_26, B_27), k3_xboole_0(A_26, C_28))=k4_xboole_0(A_26, k4_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.77/2.46  tff(c_7468, plain, (![B_27]: (k4_xboole_0('#skF_3', k4_xboole_0(B_27, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_3', B_27), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7386, c_32])).
% 6.77/2.46  tff(c_8061, plain, (![B_185]: (k4_xboole_0('#skF_3', k4_xboole_0(B_185, '#skF_2'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_2, c_7468])).
% 6.77/2.46  tff(c_8152, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_730, c_8061])).
% 6.77/2.46  tff(c_71, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.77/2.46  tff(c_74, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_71])).
% 6.77/2.46  tff(c_225, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_202])).
% 6.77/2.46  tff(c_535, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.46  tff(c_576, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=k3_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_225, c_535])).
% 6.77/2.46  tff(c_587, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_576])).
% 6.77/2.46  tff(c_3351, plain, (![A_7, B_136]: (k4_xboole_0(A_7, k4_xboole_0(B_136, A_7))=k2_xboole_0(k4_xboole_0(A_7, B_136), A_7))), inference(superposition, [status(thm), theory('equality')], [c_587, c_3249])).
% 6.77/2.46  tff(c_3582, plain, (![A_140, B_141]: (k4_xboole_0(A_140, k4_xboole_0(B_141, A_140))=A_140)), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_2, c_3351])).
% 6.77/2.46  tff(c_3696, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_730, c_3582])).
% 6.77/2.46  tff(c_516, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_491])).
% 6.77/2.46  tff(c_16, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.46  tff(c_7354, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7302, c_16])).
% 6.77/2.46  tff(c_7383, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_7354])).
% 6.77/2.46  tff(c_381, plain, (![A_59, B_60]: (k2_xboole_0(A_59, k2_xboole_0(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.46  tff(c_4101, plain, (![B_144, A_145]: (k2_xboole_0(B_144, k2_xboole_0(A_145, B_144))=k2_xboole_0(B_144, A_145))), inference(superposition, [status(thm), theory('equality')], [c_2, c_381])).
% 6.77/2.46  tff(c_4238, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45, c_4101])).
% 6.77/2.46  tff(c_4276, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_2, c_4238])).
% 6.77/2.46  tff(c_1961, plain, (![A_98, B_99, C_100]: (k2_xboole_0(k2_xboole_0(A_98, B_99), C_100)=k2_xboole_0(A_98, k2_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.77/2.46  tff(c_8199, plain, (![C_186, A_187, B_188]: (k2_xboole_0(C_186, k2_xboole_0(A_187, B_188))=k2_xboole_0(A_187, k2_xboole_0(B_188, C_186)))), inference(superposition, [status(thm), theory('equality')], [c_1961, c_2])).
% 6.77/2.46  tff(c_8496, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4276, c_8199])).
% 6.77/2.46  tff(c_8688, plain, (k2_xboole_0('#skF_4', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7383, c_8496])).
% 6.77/2.46  tff(c_9095, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8688, c_516])).
% 6.77/2.46  tff(c_9132, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8152, c_3696, c_516, c_9095])).
% 6.77/2.46  tff(c_9134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_9132])).
% 6.77/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.46  
% 6.77/2.46  Inference rules
% 6.77/2.46  ----------------------
% 6.77/2.46  #Ref     : 0
% 6.77/2.46  #Sup     : 2334
% 6.77/2.46  #Fact    : 0
% 6.77/2.46  #Define  : 0
% 6.77/2.46  #Split   : 0
% 6.77/2.46  #Chain   : 0
% 6.77/2.46  #Close   : 0
% 6.77/2.46  
% 6.77/2.46  Ordering : KBO
% 6.77/2.46  
% 6.77/2.46  Simplification rules
% 6.77/2.46  ----------------------
% 6.77/2.46  #Subsume      : 15
% 6.77/2.46  #Demod        : 2129
% 6.77/2.46  #Tautology    : 1698
% 6.77/2.46  #SimpNegUnit  : 1
% 6.77/2.46  #BackRed      : 0
% 6.77/2.46  
% 6.77/2.46  #Partial instantiations: 0
% 6.77/2.46  #Strategies tried      : 1
% 6.77/2.46  
% 6.77/2.46  Timing (in seconds)
% 6.77/2.46  ----------------------
% 6.77/2.47  Preprocessing        : 0.32
% 6.77/2.47  Parsing              : 0.18
% 6.77/2.47  CNF conversion       : 0.02
% 6.77/2.47  Main loop            : 1.36
% 6.77/2.47  Inferencing          : 0.38
% 6.77/2.47  Reduction            : 0.66
% 6.77/2.47  Demodulation         : 0.56
% 6.77/2.47  BG Simplification    : 0.04
% 6.77/2.47  Subsumption          : 0.21
% 6.77/2.47  Abstraction          : 0.05
% 6.77/2.47  MUC search           : 0.00
% 6.77/2.47  Cooper               : 0.00
% 6.77/2.47  Total                : 1.72
% 6.77/2.47  Index Insertion      : 0.00
% 6.77/2.47  Index Deletion       : 0.00
% 6.77/2.47  Index Matching       : 0.00
% 6.77/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
