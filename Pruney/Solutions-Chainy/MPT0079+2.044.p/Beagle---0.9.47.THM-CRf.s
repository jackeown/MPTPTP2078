%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:48 EST 2020

% Result     : Theorem 9.89s
% Output     : CNFRefutation 9.89s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 471 expanded)
%              Number of leaves         :   30 ( 173 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 592 expanded)
%              Number of equality atoms :   72 ( 425 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_243,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_434,plain,(
    ! [A_52,B_53] :
      ( ~ r1_xboole_0(A_52,B_53)
      | k3_xboole_0(A_52,B_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_243])).

tff(c_450,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_434])).

tff(c_478,plain,(
    ! [A_54,B_55] : k2_xboole_0(k3_xboole_0(A_54,B_55),k4_xboole_0(A_54,B_55)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_493,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_3')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_478])).

tff(c_84,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_100,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_14])).

tff(c_593,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_100])).

tff(c_197,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_203,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_447,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_203,c_434])).

tff(c_496,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_478])).

tff(c_919,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_100])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_449,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_434])).

tff(c_30,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(A_29,B_30),k4_xboole_0(A_29,B_30)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_522,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_6','#skF_4')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_30])).

tff(c_564,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_39,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_184,plain,(
    k2_xboole_0('#skF_6','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_2])).

tff(c_16,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_614,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_660,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_614])).

tff(c_667,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_660])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_813,plain,(
    ! [A_62,B_63,C_64] : k2_xboole_0(k2_xboole_0(A_62,B_63),C_64) = k2_xboole_0(A_62,k2_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1023,plain,(
    ! [A_69,C_70] : k2_xboole_0(A_69,k2_xboole_0(A_69,C_70)) = k2_xboole_0(A_69,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_813])).

tff(c_1042,plain,(
    ! [A_69,C_70] : k4_xboole_0(k2_xboole_0(A_69,C_70),k2_xboole_0(A_69,C_70)) = k4_xboole_0(A_69,k2_xboole_0(A_69,C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_22])).

tff(c_1188,plain,(
    ! [A_75,C_76] : k4_xboole_0(A_75,k2_xboole_0(A_75,C_76)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_1042])).

tff(c_1222,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_1188])).

tff(c_1419,plain,(
    ! [A_81,B_82,C_83] : k4_xboole_0(k4_xboole_0(A_81,B_82),C_83) = k4_xboole_0(A_81,k2_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18347,plain,(
    ! [C_241,A_242,B_243] : k2_xboole_0(C_241,k4_xboole_0(A_242,k2_xboole_0(B_243,C_241))) = k2_xboole_0(C_241,k4_xboole_0(A_242,B_243)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1419,c_18])).

tff(c_18629,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_6','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_18347])).

tff(c_18778,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_14,c_18629])).

tff(c_1231,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1188])).

tff(c_19214,plain,(
    ! [A_244] : k2_xboole_0('#skF_6',k4_xboole_0(A_244,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_6',k4_xboole_0(A_244,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_18347])).

tff(c_19374,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_19214])).

tff(c_19437,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18778,c_2,c_919,c_14,c_19374])).

tff(c_260,plain,(
    ! [A_47,B_48] : k4_xboole_0(k2_xboole_0(A_47,B_48),B_48) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16796,plain,(
    ! [A_236,B_237] : k4_xboole_0(k2_xboole_0(A_236,B_237),k4_xboole_0(B_237,A_236)) = k4_xboole_0(A_236,k4_xboole_0(B_237,A_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_260])).

tff(c_17096,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k4_xboole_0('#skF_6','#skF_5')) = k4_xboole_0('#skF_5',k4_xboole_0('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_16796])).

tff(c_19451,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k4_xboole_0('#skF_3','#skF_5')) = k4_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19437,c_19437,c_17096])).

tff(c_19492,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_919,c_22,c_919,c_19451])).

tff(c_202,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_197])).

tff(c_448,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_202,c_434])).

tff(c_19482,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19437,c_448])).

tff(c_1341,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k2_xboole_0(B_80,A_79)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1188])).

tff(c_1750,plain,(
    ! [A_88,B_89] : k4_xboole_0(k4_xboole_0(A_88,B_89),A_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1341])).

tff(c_1770,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = k2_xboole_0(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1750,c_18])).

tff(c_1847,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1770])).

tff(c_630,plain,(
    ! [A_56,B_57] : k2_xboole_0(k4_xboole_0(A_56,B_57),k3_xboole_0(A_56,B_57)) = k2_xboole_0(k4_xboole_0(A_56,B_57),A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_18])).

tff(c_662,plain,(
    ! [A_56,B_57] : k2_xboole_0(k4_xboole_0(A_56,B_57),k3_xboole_0(A_56,B_57)) = k2_xboole_0(A_56,k4_xboole_0(A_56,B_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_630])).

tff(c_11067,plain,(
    ! [A_56,B_57] : k2_xboole_0(k4_xboole_0(A_56,B_57),k3_xboole_0(A_56,B_57)) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_662])).

tff(c_20149,plain,(
    k2_xboole_0(k4_xboole_0('#skF_4','#skF_3'),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_19482,c_11067])).

tff(c_20192,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_19492,c_20149])).

tff(c_20194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.89/3.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.94  
% 9.89/3.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.94  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 9.89/3.94  
% 9.89/3.94  %Foreground sorts:
% 9.89/3.94  
% 9.89/3.94  
% 9.89/3.94  %Background operators:
% 9.89/3.94  
% 9.89/3.94  
% 9.89/3.94  %Foreground operators:
% 9.89/3.94  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.89/3.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.89/3.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.89/3.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.89/3.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.89/3.94  tff('#skF_5', type, '#skF_5': $i).
% 9.89/3.94  tff('#skF_6', type, '#skF_6': $i).
% 9.89/3.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.89/3.94  tff('#skF_3', type, '#skF_3': $i).
% 9.89/3.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.89/3.94  tff('#skF_4', type, '#skF_4': $i).
% 9.89/3.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.89/3.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.89/3.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.89/3.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.89/3.94  
% 9.89/3.96  tff(f_82, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 9.89/3.96  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 9.89/3.96  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.89/3.96  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.89/3.96  tff(f_73, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 9.89/3.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.89/3.96  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.89/3.96  tff(f_65, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 9.89/3.96  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.89/3.96  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.89/3.96  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.89/3.96  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.89/3.96  tff(f_71, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 9.89/3.96  tff(f_67, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.89/3.96  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.89/3.96  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.89/3.96  tff(c_14, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.89/3.96  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.89/3.96  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.89/3.96  tff(c_243, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.89/3.96  tff(c_434, plain, (![A_52, B_53]: (~r1_xboole_0(A_52, B_53) | k3_xboole_0(A_52, B_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_243])).
% 9.89/3.96  tff(c_450, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_434])).
% 9.89/3.96  tff(c_478, plain, (![A_54, B_55]: (k2_xboole_0(k3_xboole_0(A_54, B_55), k4_xboole_0(A_54, B_55))=A_54)), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.89/3.96  tff(c_493, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_3'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_450, c_478])).
% 9.89/3.96  tff(c_84, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.89/3.96  tff(c_100, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_84, c_14])).
% 9.89/3.96  tff(c_593, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_493, c_100])).
% 9.89/3.96  tff(c_197, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.89/3.96  tff(c_203, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_197])).
% 9.89/3.96  tff(c_447, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_203, c_434])).
% 9.89/3.96  tff(c_496, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_447, c_478])).
% 9.89/3.96  tff(c_919, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_496, c_100])).
% 9.89/3.96  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.89/3.96  tff(c_34, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.89/3.96  tff(c_449, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_434])).
% 9.89/3.96  tff(c_30, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(A_29, B_30), k4_xboole_0(A_29, B_30))=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.89/3.96  tff(c_522, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_6', '#skF_4'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_449, c_30])).
% 9.89/3.96  tff(c_564, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_522, c_100])).
% 9.89/3.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.89/3.96  tff(c_38, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.89/3.96  tff(c_39, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 9.89/3.96  tff(c_184, plain, (k2_xboole_0('#skF_6', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39, c_2])).
% 9.89/3.96  tff(c_16, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.89/3.96  tff(c_20, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.89/3.96  tff(c_614, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.89/3.96  tff(c_660, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_614])).
% 9.89/3.96  tff(c_667, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_660])).
% 9.89/3.96  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.89/3.96  tff(c_813, plain, (![A_62, B_63, C_64]: (k2_xboole_0(k2_xboole_0(A_62, B_63), C_64)=k2_xboole_0(A_62, k2_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.89/3.96  tff(c_1023, plain, (![A_69, C_70]: (k2_xboole_0(A_69, k2_xboole_0(A_69, C_70))=k2_xboole_0(A_69, C_70))), inference(superposition, [status(thm), theory('equality')], [c_4, c_813])).
% 9.89/3.96  tff(c_1042, plain, (![A_69, C_70]: (k4_xboole_0(k2_xboole_0(A_69, C_70), k2_xboole_0(A_69, C_70))=k4_xboole_0(A_69, k2_xboole_0(A_69, C_70)))), inference(superposition, [status(thm), theory('equality')], [c_1023, c_22])).
% 9.89/3.96  tff(c_1188, plain, (![A_75, C_76]: (k4_xboole_0(A_75, k2_xboole_0(A_75, C_76))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_667, c_1042])).
% 9.89/3.96  tff(c_1222, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_184, c_1188])).
% 9.89/3.96  tff(c_1419, plain, (![A_81, B_82, C_83]: (k4_xboole_0(k4_xboole_0(A_81, B_82), C_83)=k4_xboole_0(A_81, k2_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.89/3.96  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.89/3.96  tff(c_18347, plain, (![C_241, A_242, B_243]: (k2_xboole_0(C_241, k4_xboole_0(A_242, k2_xboole_0(B_243, C_241)))=k2_xboole_0(C_241, k4_xboole_0(A_242, B_243)))), inference(superposition, [status(thm), theory('equality')], [c_1419, c_18])).
% 9.89/3.96  tff(c_18629, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1222, c_18347])).
% 9.89/3.96  tff(c_18778, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_564, c_14, c_18629])).
% 9.89/3.96  tff(c_1231, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1188])).
% 9.89/3.96  tff(c_19214, plain, (![A_244]: (k2_xboole_0('#skF_6', k4_xboole_0(A_244, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_6', k4_xboole_0(A_244, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_39, c_18347])).
% 9.89/3.96  tff(c_19374, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1231, c_19214])).
% 9.89/3.96  tff(c_19437, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18778, c_2, c_919, c_14, c_19374])).
% 9.89/3.96  tff(c_260, plain, (![A_47, B_48]: (k4_xboole_0(k2_xboole_0(A_47, B_48), B_48)=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.89/3.96  tff(c_16796, plain, (![A_236, B_237]: (k4_xboole_0(k2_xboole_0(A_236, B_237), k4_xboole_0(B_237, A_236))=k4_xboole_0(A_236, k4_xboole_0(B_237, A_236)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_260])).
% 9.89/3.96  tff(c_17096, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k4_xboole_0('#skF_6', '#skF_5'))=k4_xboole_0('#skF_5', k4_xboole_0('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_16796])).
% 9.89/3.96  tff(c_19451, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k4_xboole_0('#skF_3', '#skF_5'))=k4_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_19437, c_19437, c_17096])).
% 9.89/3.96  tff(c_19492, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_919, c_22, c_919, c_19451])).
% 9.89/3.96  tff(c_202, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_197])).
% 9.89/3.96  tff(c_448, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_202, c_434])).
% 9.89/3.96  tff(c_19482, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_19437, c_448])).
% 9.89/3.96  tff(c_1341, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k2_xboole_0(B_80, A_79))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1188])).
% 9.89/3.96  tff(c_1750, plain, (![A_88, B_89]: (k4_xboole_0(k4_xboole_0(A_88, B_89), A_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_1341])).
% 9.89/3.96  tff(c_1770, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(A_88, B_89))=k2_xboole_0(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1750, c_18])).
% 9.89/3.96  tff(c_1847, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(A_88, B_89))=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1770])).
% 9.89/3.96  tff(c_630, plain, (![A_56, B_57]: (k2_xboole_0(k4_xboole_0(A_56, B_57), k3_xboole_0(A_56, B_57))=k2_xboole_0(k4_xboole_0(A_56, B_57), A_56))), inference(superposition, [status(thm), theory('equality')], [c_614, c_18])).
% 9.89/3.96  tff(c_662, plain, (![A_56, B_57]: (k2_xboole_0(k4_xboole_0(A_56, B_57), k3_xboole_0(A_56, B_57))=k2_xboole_0(A_56, k4_xboole_0(A_56, B_57)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_630])).
% 9.89/3.96  tff(c_11067, plain, (![A_56, B_57]: (k2_xboole_0(k4_xboole_0(A_56, B_57), k3_xboole_0(A_56, B_57))=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_662])).
% 9.89/3.96  tff(c_20149, plain, (k2_xboole_0(k4_xboole_0('#skF_4', '#skF_3'), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_19482, c_11067])).
% 9.89/3.96  tff(c_20192, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_19492, c_20149])).
% 9.89/3.96  tff(c_20194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_20192])).
% 9.89/3.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.96  
% 9.89/3.96  Inference rules
% 9.89/3.96  ----------------------
% 9.89/3.96  #Ref     : 0
% 9.89/3.96  #Sup     : 5144
% 9.89/3.96  #Fact    : 0
% 9.89/3.96  #Define  : 0
% 9.89/3.96  #Split   : 1
% 9.89/3.96  #Chain   : 0
% 9.89/3.96  #Close   : 0
% 9.89/3.96  
% 9.89/3.96  Ordering : KBO
% 9.89/3.96  
% 9.89/3.96  Simplification rules
% 9.89/3.96  ----------------------
% 9.89/3.96  #Subsume      : 104
% 9.89/3.96  #Demod        : 5900
% 9.89/3.96  #Tautology    : 3227
% 9.89/3.96  #SimpNegUnit  : 26
% 9.89/3.96  #BackRed      : 53
% 9.89/3.96  
% 9.89/3.96  #Partial instantiations: 0
% 9.89/3.96  #Strategies tried      : 1
% 9.89/3.96  
% 9.89/3.96  Timing (in seconds)
% 9.89/3.96  ----------------------
% 9.89/3.96  Preprocessing        : 0.30
% 9.89/3.96  Parsing              : 0.16
% 9.89/3.96  CNF conversion       : 0.02
% 9.89/3.96  Main loop            : 2.92
% 9.89/3.96  Inferencing          : 0.56
% 9.89/3.96  Reduction            : 1.73
% 9.89/3.96  Demodulation         : 1.55
% 9.89/3.96  BG Simplification    : 0.07
% 9.89/3.96  Subsumption          : 0.42
% 9.89/3.96  Abstraction          : 0.10
% 9.89/3.96  MUC search           : 0.00
% 9.89/3.96  Cooper               : 0.00
% 9.89/3.96  Total                : 3.25
% 9.89/3.96  Index Insertion      : 0.00
% 9.89/3.96  Index Deletion       : 0.00
% 9.89/3.97  Index Matching       : 0.00
% 9.89/3.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
