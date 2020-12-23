%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:48 EST 2020

% Result     : Theorem 8.16s
% Output     : CNFRefutation 8.16s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 376 expanded)
%              Number of leaves         :   31 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 484 expanded)
%              Number of equality atoms :   66 ( 321 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_36,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_113,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_141,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_18])).

tff(c_38,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_933,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_973,plain,(
    ! [A_82,B_83] :
      ( ~ r1_xboole_0(A_82,B_83)
      | k3_xboole_0(A_82,B_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_933])).

tff(c_988,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_973])).

tff(c_26,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1604,plain,(
    ! [A_102,B_103,C_104] : k4_xboole_0(k4_xboole_0(A_102,B_103),C_104) = k4_xboole_0(A_102,k2_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1686,plain,(
    ! [A_25,B_26,C_104] : k4_xboole_0(A_25,k2_xboole_0(k3_xboole_0(A_25,B_26),C_104)) = k4_xboole_0(k4_xboole_0(A_25,B_26),C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1604])).

tff(c_10802,plain,(
    ! [A_181,B_182,C_183] : k4_xboole_0(A_181,k2_xboole_0(k3_xboole_0(A_181,B_182),C_183)) = k4_xboole_0(A_181,k2_xboole_0(B_182,C_183)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1686])).

tff(c_10942,plain,(
    ! [C_183] : k4_xboole_0('#skF_6',k2_xboole_0(k1_xboole_0,C_183)) = k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_10802])).

tff(c_11181,plain,(
    ! [C_185] : k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_185)) = k4_xboole_0('#skF_6',C_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_10942])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_43,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_34,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_134,plain,(
    ! [A_44,B_43] : r1_tarski(A_44,k2_xboole_0(B_43,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_34])).

tff(c_273,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_383,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k2_xboole_0(B_58,A_57)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_273])).

tff(c_414,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_383])).

tff(c_11226,plain,(
    k4_xboole_0('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11181,c_414])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1276,plain,(
    ! [A_90,B_91,C_92] : k2_xboole_0(k2_xboole_0(A_90,B_91),C_92) = k2_xboole_0(A_90,k2_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1373,plain,(
    ! [A_3,C_92] : k2_xboole_0(A_3,k2_xboole_0(A_3,C_92)) = k2_xboole_0(A_3,C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1276])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3738,plain,(
    ! [C_134,A_135,B_136] : k2_xboole_0(C_134,k2_xboole_0(A_135,B_136)) = k2_xboole_0(A_135,k2_xboole_0(B_136,C_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_2])).

tff(c_4746,plain,(
    ! [A_142,C_143] : k2_xboole_0(A_142,k2_xboole_0(A_142,C_143)) = k2_xboole_0(C_143,A_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3738])).

tff(c_4962,plain,(
    ! [B_18,A_17] : k2_xboole_0(k4_xboole_0(B_18,A_17),A_17) = k2_xboole_0(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4746])).

tff(c_5042,plain,(
    ! [B_18,A_17] : k2_xboole_0(k4_xboole_0(B_18,A_17),A_17) = k2_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_4962])).

tff(c_11336,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k2_xboole_0('#skF_3','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11226,c_5042])).

tff(c_11360,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_11336])).

tff(c_22,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_98,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_986,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_973])).

tff(c_996,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_28])).

tff(c_1001,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_996])).

tff(c_297,plain,(
    ! [A_44,B_43] : k4_xboole_0(A_44,k2_xboole_0(B_43,A_44)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_273])).

tff(c_11534,plain,(
    ! [C_186,A_187,B_188] : k2_xboole_0(C_186,k4_xboole_0(A_187,k2_xboole_0(B_188,C_186))) = k2_xboole_0(C_186,k4_xboole_0(A_187,B_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_20])).

tff(c_12175,plain,(
    ! [A_189] : k2_xboole_0('#skF_6',k4_xboole_0(A_189,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_6',k4_xboole_0(A_189,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_11534])).

tff(c_12331,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_12175])).

tff(c_12380,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11360,c_2,c_1001,c_18,c_12331])).

tff(c_103,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_987,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_973])).

tff(c_1009,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_28])).

tff(c_1014,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1009])).

tff(c_12412,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12380,c_1014])).

tff(c_989,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_973])).

tff(c_1109,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_989,c_28])).

tff(c_1116,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1109])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_465,plain,(
    ! [A_61,B_62] : k4_xboole_0(k2_xboole_0(A_61,B_62),B_62) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_490,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_465])).

tff(c_12419,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12380,c_12380,c_490])).

tff(c_12450,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_24,c_12419])).

tff(c_13023,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12412,c_12450])).

tff(c_13024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_13023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:01:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.16/3.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/3.11  
% 8.16/3.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/3.12  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 8.16/3.12  
% 8.16/3.12  %Foreground sorts:
% 8.16/3.12  
% 8.16/3.12  
% 8.16/3.12  %Background operators:
% 8.16/3.12  
% 8.16/3.12  
% 8.16/3.12  %Foreground operators:
% 8.16/3.12  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.16/3.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.16/3.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.16/3.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.16/3.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.16/3.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.16/3.12  tff('#skF_5', type, '#skF_5': $i).
% 8.16/3.12  tff('#skF_6', type, '#skF_6': $i).
% 8.16/3.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.16/3.12  tff('#skF_3', type, '#skF_3': $i).
% 8.16/3.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.16/3.12  tff('#skF_4', type, '#skF_4': $i).
% 8.16/3.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.16/3.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.16/3.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.16/3.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.16/3.12  
% 8.16/3.13  tff(f_86, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.16/3.13  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.16/3.13  tff(f_61, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.16/3.13  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.16/3.13  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.16/3.13  tff(f_69, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.16/3.13  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.16/3.13  tff(f_77, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.16/3.13  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.16/3.13  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.16/3.13  tff(f_75, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 8.16/3.13  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.16/3.13  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.16/3.13  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.16/3.13  tff(f_67, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.16/3.13  tff(c_36, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.16/3.13  tff(c_113, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.16/3.13  tff(c_18, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.16/3.13  tff(c_141, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_113, c_18])).
% 8.16/3.13  tff(c_38, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.16/3.13  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.16/3.13  tff(c_933, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.16/3.13  tff(c_973, plain, (![A_82, B_83]: (~r1_xboole_0(A_82, B_83) | k3_xboole_0(A_82, B_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_933])).
% 8.16/3.13  tff(c_988, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_973])).
% 8.16/3.13  tff(c_26, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.16/3.13  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.16/3.13  tff(c_1604, plain, (![A_102, B_103, C_104]: (k4_xboole_0(k4_xboole_0(A_102, B_103), C_104)=k4_xboole_0(A_102, k2_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.16/3.13  tff(c_1686, plain, (![A_25, B_26, C_104]: (k4_xboole_0(A_25, k2_xboole_0(k3_xboole_0(A_25, B_26), C_104))=k4_xboole_0(k4_xboole_0(A_25, B_26), C_104))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1604])).
% 8.16/3.13  tff(c_10802, plain, (![A_181, B_182, C_183]: (k4_xboole_0(A_181, k2_xboole_0(k3_xboole_0(A_181, B_182), C_183))=k4_xboole_0(A_181, k2_xboole_0(B_182, C_183)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1686])).
% 8.16/3.13  tff(c_10942, plain, (![C_183]: (k4_xboole_0('#skF_6', k2_xboole_0(k1_xboole_0, C_183))=k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_183)))), inference(superposition, [status(thm), theory('equality')], [c_988, c_10802])).
% 8.16/3.13  tff(c_11181, plain, (![C_185]: (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_185))=k4_xboole_0('#skF_6', C_185))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_10942])).
% 8.16/3.13  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.16/3.13  tff(c_42, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.16/3.13  tff(c_43, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 8.16/3.13  tff(c_34, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.16/3.13  tff(c_134, plain, (![A_44, B_43]: (r1_tarski(A_44, k2_xboole_0(B_43, A_44)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_34])).
% 8.16/3.13  tff(c_273, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.16/3.13  tff(c_383, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k2_xboole_0(B_58, A_57))=k1_xboole_0)), inference(resolution, [status(thm)], [c_134, c_273])).
% 8.16/3.13  tff(c_414, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_43, c_383])).
% 8.16/3.13  tff(c_11226, plain, (k4_xboole_0('#skF_6', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11181, c_414])).
% 8.16/3.13  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.16/3.13  tff(c_1276, plain, (![A_90, B_91, C_92]: (k2_xboole_0(k2_xboole_0(A_90, B_91), C_92)=k2_xboole_0(A_90, k2_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.16/3.13  tff(c_1373, plain, (![A_3, C_92]: (k2_xboole_0(A_3, k2_xboole_0(A_3, C_92))=k2_xboole_0(A_3, C_92))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1276])).
% 8.16/3.13  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.16/3.13  tff(c_3738, plain, (![C_134, A_135, B_136]: (k2_xboole_0(C_134, k2_xboole_0(A_135, B_136))=k2_xboole_0(A_135, k2_xboole_0(B_136, C_134)))), inference(superposition, [status(thm), theory('equality')], [c_1276, c_2])).
% 8.16/3.13  tff(c_4746, plain, (![A_142, C_143]: (k2_xboole_0(A_142, k2_xboole_0(A_142, C_143))=k2_xboole_0(C_143, A_142))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3738])).
% 8.16/3.13  tff(c_4962, plain, (![B_18, A_17]: (k2_xboole_0(k4_xboole_0(B_18, A_17), A_17)=k2_xboole_0(A_17, k2_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4746])).
% 8.16/3.13  tff(c_5042, plain, (![B_18, A_17]: (k2_xboole_0(k4_xboole_0(B_18, A_17), A_17)=k2_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_1373, c_4962])).
% 8.16/3.13  tff(c_11336, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k2_xboole_0('#skF_3', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11226, c_5042])).
% 8.16/3.13  tff(c_11360, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_11336])).
% 8.16/3.13  tff(c_22, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.16/3.13  tff(c_40, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.16/3.13  tff(c_98, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.16/3.13  tff(c_104, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_98])).
% 8.16/3.13  tff(c_986, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_973])).
% 8.16/3.13  tff(c_996, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_986, c_28])).
% 8.16/3.13  tff(c_1001, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_996])).
% 8.16/3.13  tff(c_297, plain, (![A_44, B_43]: (k4_xboole_0(A_44, k2_xboole_0(B_43, A_44))=k1_xboole_0)), inference(resolution, [status(thm)], [c_134, c_273])).
% 8.16/3.13  tff(c_11534, plain, (![C_186, A_187, B_188]: (k2_xboole_0(C_186, k4_xboole_0(A_187, k2_xboole_0(B_188, C_186)))=k2_xboole_0(C_186, k4_xboole_0(A_187, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_1604, c_20])).
% 8.16/3.13  tff(c_12175, plain, (![A_189]: (k2_xboole_0('#skF_6', k4_xboole_0(A_189, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_6', k4_xboole_0(A_189, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_43, c_11534])).
% 8.16/3.13  tff(c_12331, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_297, c_12175])).
% 8.16/3.13  tff(c_12380, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11360, c_2, c_1001, c_18, c_12331])).
% 8.16/3.13  tff(c_103, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_98])).
% 8.16/3.13  tff(c_987, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_103, c_973])).
% 8.16/3.13  tff(c_1009, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_987, c_28])).
% 8.16/3.13  tff(c_1014, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1009])).
% 8.16/3.13  tff(c_12412, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12380, c_1014])).
% 8.16/3.13  tff(c_989, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_973])).
% 8.16/3.13  tff(c_1109, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_989, c_28])).
% 8.16/3.13  tff(c_1116, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1109])).
% 8.16/3.13  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.16/3.13  tff(c_465, plain, (![A_61, B_62]: (k4_xboole_0(k2_xboole_0(A_61, B_62), B_62)=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.16/3.13  tff(c_490, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_43, c_465])).
% 8.16/3.13  tff(c_12419, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12380, c_12380, c_490])).
% 8.16/3.13  tff(c_12450, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_24, c_12419])).
% 8.16/3.13  tff(c_13023, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12412, c_12450])).
% 8.16/3.13  tff(c_13024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_13023])).
% 8.16/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/3.13  
% 8.16/3.13  Inference rules
% 8.16/3.13  ----------------------
% 8.16/3.13  #Ref     : 0
% 8.16/3.13  #Sup     : 3223
% 8.16/3.13  #Fact    : 0
% 8.16/3.13  #Define  : 0
% 8.16/3.13  #Split   : 2
% 8.16/3.13  #Chain   : 0
% 8.16/3.13  #Close   : 0
% 8.16/3.13  
% 8.16/3.13  Ordering : KBO
% 8.16/3.13  
% 8.16/3.13  Simplification rules
% 8.16/3.13  ----------------------
% 8.16/3.13  #Subsume      : 90
% 8.16/3.13  #Demod        : 3632
% 8.16/3.13  #Tautology    : 1907
% 8.16/3.13  #SimpNegUnit  : 9
% 8.16/3.13  #BackRed      : 44
% 8.16/3.13  
% 8.16/3.13  #Partial instantiations: 0
% 8.16/3.13  #Strategies tried      : 1
% 8.16/3.13  
% 8.16/3.13  Timing (in seconds)
% 8.16/3.13  ----------------------
% 8.16/3.14  Preprocessing        : 0.31
% 8.16/3.14  Parsing              : 0.17
% 8.16/3.14  CNF conversion       : 0.02
% 8.16/3.14  Main loop            : 2.06
% 8.16/3.14  Inferencing          : 0.42
% 8.16/3.14  Reduction            : 1.21
% 8.16/3.14  Demodulation         : 1.08
% 8.16/3.14  BG Simplification    : 0.05
% 8.16/3.14  Subsumption          : 0.28
% 8.16/3.14  Abstraction          : 0.07
% 8.16/3.14  MUC search           : 0.00
% 8.16/3.14  Cooper               : 0.00
% 8.16/3.14  Total                : 2.41
% 8.16/3.14  Index Insertion      : 0.00
% 8.16/3.14  Index Deletion       : 0.00
% 8.16/3.14  Index Matching       : 0.00
% 8.16/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
