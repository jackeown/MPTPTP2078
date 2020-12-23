%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:20 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 473 expanded)
%              Number of leaves         :   25 ( 168 expanded)
%              Depth                    :   17
%              Number of atoms          :   90 ( 527 expanded)
%              Number of equality atoms :   60 ( 379 expanded)
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

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_587,plain,(
    ! [A_67,B_68] :
      ( r1_xboole_0(A_67,B_68)
      | k4_xboole_0(A_67,B_68) != A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_452,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_489,plain,(
    ! [A_59,A_60,B_61] :
      ( r1_tarski(A_59,A_60)
      | ~ r1_tarski(A_59,k4_xboole_0(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_10,c_452])).

tff(c_526,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_489])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_526])).

tff(c_540,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_595,plain,(
    k4_xboole_0('#skF_1','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_587,c_540])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_45])).

tff(c_542,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_556,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_48,c_542])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_642,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_660,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_642])).

tff(c_664,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_660])).

tff(c_596,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_614,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_596])).

tff(c_618,plain,(
    ! [A_71] : k4_xboole_0(A_71,A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_614])).

tff(c_665,plain,(
    ! [A_74] : r1_tarski(k1_xboole_0,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_10])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_696,plain,(
    ! [A_77] : k3_xboole_0(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_665,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_701,plain,(
    ! [A_77] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_2])).

tff(c_719,plain,(
    ! [A_77] : k4_xboole_0(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_701])).

tff(c_2046,plain,(
    ! [A_128,B_129,C_130] : k2_xboole_0(k4_xboole_0(A_128,B_129),k3_xboole_0(A_128,C_130)) = k4_xboole_0(A_128,k4_xboole_0(B_129,C_130)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2103,plain,(
    ! [A_11,C_130] : k4_xboole_0(A_11,k4_xboole_0(k1_xboole_0,C_130)) = k2_xboole_0(A_11,k3_xboole_0(A_11,C_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2046])).

tff(c_2111,plain,(
    ! [A_131,C_132] : k2_xboole_0(A_131,k3_xboole_0(A_131,C_132)) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_719,c_2103])).

tff(c_2138,plain,(
    ! [A_11] : k2_xboole_0(A_11,A_11) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_2111])).

tff(c_617,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_614])).

tff(c_654,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k4_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_642])).

tff(c_663,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_654])).

tff(c_1624,plain,(
    ! [A_118,B_119] : k5_xboole_0(k5_xboole_0(A_118,B_119),k2_xboole_0(A_118,B_119)) = k3_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1658,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_11,A_11)) = k3_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_1624])).

tff(c_1667,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_11,A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_1658])).

tff(c_2166,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_1667])).

tff(c_669,plain,(
    ! [A_74] : k3_xboole_0(k1_xboole_0,A_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_665,c_6])).

tff(c_541,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_555,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_541,c_542])).

tff(c_657,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_642])).

tff(c_820,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_657])).

tff(c_558,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_542])).

tff(c_651,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_642])).

tff(c_1259,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_651])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k2_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10194,plain,(
    ! [A_262,B_263,C_264] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_262,B_263),k3_xboole_0(A_262,C_264)),k4_xboole_0(A_262,k4_xboole_0(B_263,C_264))) = k3_xboole_0(k4_xboole_0(A_262,B_263),k3_xboole_0(A_262,C_264)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2046,c_24])).

tff(c_10380,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')),k1_xboole_0) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1259,c_10194])).

tff(c_10484,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2166,c_669,c_820,c_664,c_820,c_10380])).

tff(c_1039,plain,(
    ! [A_98,B_99,C_100] : k5_xboole_0(k5_xboole_0(A_98,B_99),C_100) = k5_xboole_0(A_98,k5_xboole_0(B_99,C_100)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4370,plain,(
    ! [A_178,B_179,C_180] : k5_xboole_0(A_178,k5_xboole_0(k3_xboole_0(A_178,B_179),C_180)) = k5_xboole_0(k4_xboole_0(A_178,B_179),C_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1039])).

tff(c_4479,plain,(
    ! [A_178,B_179] : k5_xboole_0(k4_xboole_0(A_178,B_179),k3_xboole_0(A_178,B_179)) = k5_xboole_0(A_178,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_4370])).

tff(c_4606,plain,(
    ! [A_183,B_184] : k5_xboole_0(k4_xboole_0(A_183,B_184),k3_xboole_0(A_183,B_184)) = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_4479])).

tff(c_1070,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k5_xboole_0(B_99,k5_xboole_0(A_98,B_99))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_1039])).

tff(c_1066,plain,(
    ! [A_11,C_100] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_100)) = k5_xboole_0(k1_xboole_0,C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_1039])).

tff(c_3475,plain,(
    ! [A_158,C_159] : k5_xboole_0(A_158,k5_xboole_0(A_158,C_159)) = C_159 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2166,c_1066])).

tff(c_3519,plain,(
    ! [B_99,A_98] : k5_xboole_0(B_99,k5_xboole_0(A_98,B_99)) = k5_xboole_0(A_98,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_3475])).

tff(c_3568,plain,(
    ! [B_99,A_98] : k5_xboole_0(B_99,k5_xboole_0(A_98,B_99)) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_3519])).

tff(c_4624,plain,(
    ! [A_183,B_184] : k5_xboole_0(k3_xboole_0(A_183,B_184),A_183) = k4_xboole_0(A_183,B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_4606,c_3568])).

tff(c_10518,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_1') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10484,c_4624])).

tff(c_10588,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2166,c_10518])).

tff(c_10590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_10588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.50  
% 6.71/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.50  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.71/2.50  
% 6.71/2.50  %Foreground sorts:
% 6.71/2.50  
% 6.71/2.50  
% 6.71/2.50  %Background operators:
% 6.71/2.50  
% 6.71/2.50  
% 6.71/2.50  %Foreground operators:
% 6.71/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.71/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.71/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.71/2.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.71/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.71/2.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.71/2.50  tff('#skF_2', type, '#skF_2': $i).
% 6.71/2.50  tff('#skF_3', type, '#skF_3': $i).
% 6.71/2.50  tff('#skF_1', type, '#skF_1': $i).
% 6.71/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.71/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.71/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.71/2.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.71/2.50  
% 6.99/2.52  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.99/2.52  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.99/2.52  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.99/2.52  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.99/2.52  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.99/2.52  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.99/2.52  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.99/2.52  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.99/2.52  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.99/2.52  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.99/2.52  tff(f_55, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.99/2.52  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.99/2.52  tff(c_587, plain, (![A_67, B_68]: (r1_xboole_0(A_67, B_68) | k4_xboole_0(A_67, B_68)!=A_67)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.99/2.52  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.99/2.52  tff(c_50, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 6.99/2.52  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.99/2.52  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.99/2.52  tff(c_452, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.99/2.52  tff(c_489, plain, (![A_59, A_60, B_61]: (r1_tarski(A_59, A_60) | ~r1_tarski(A_59, k4_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_10, c_452])).
% 6.99/2.52  tff(c_526, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_489])).
% 6.99/2.52  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_526])).
% 6.99/2.52  tff(c_540, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 6.99/2.52  tff(c_595, plain, (k4_xboole_0('#skF_1', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_587, c_540])).
% 6.99/2.52  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.99/2.52  tff(c_45, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.99/2.52  tff(c_48, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_45])).
% 6.99/2.52  tff(c_542, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.99/2.52  tff(c_556, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(resolution, [status(thm)], [c_48, c_542])).
% 6.99/2.52  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.99/2.52  tff(c_642, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.99/2.52  tff(c_660, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_642])).
% 6.99/2.52  tff(c_664, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_660])).
% 6.99/2.52  tff(c_596, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.99/2.52  tff(c_614, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_596])).
% 6.99/2.52  tff(c_618, plain, (![A_71]: (k4_xboole_0(A_71, A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_614])).
% 6.99/2.52  tff(c_665, plain, (![A_74]: (r1_tarski(k1_xboole_0, A_74))), inference(superposition, [status(thm), theory('equality')], [c_618, c_10])).
% 6.99/2.52  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.99/2.52  tff(c_696, plain, (![A_77]: (k3_xboole_0(k1_xboole_0, A_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_665, c_6])).
% 6.99/2.52  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.99/2.52  tff(c_701, plain, (![A_77]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_77))), inference(superposition, [status(thm), theory('equality')], [c_696, c_2])).
% 6.99/2.52  tff(c_719, plain, (![A_77]: (k4_xboole_0(k1_xboole_0, A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_664, c_701])).
% 6.99/2.52  tff(c_2046, plain, (![A_128, B_129, C_130]: (k2_xboole_0(k4_xboole_0(A_128, B_129), k3_xboole_0(A_128, C_130))=k4_xboole_0(A_128, k4_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.99/2.52  tff(c_2103, plain, (![A_11, C_130]: (k4_xboole_0(A_11, k4_xboole_0(k1_xboole_0, C_130))=k2_xboole_0(A_11, k3_xboole_0(A_11, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2046])).
% 6.99/2.52  tff(c_2111, plain, (![A_131, C_132]: (k2_xboole_0(A_131, k3_xboole_0(A_131, C_132))=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_719, c_2103])).
% 6.99/2.52  tff(c_2138, plain, (![A_11]: (k2_xboole_0(A_11, A_11)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_556, c_2111])).
% 6.99/2.52  tff(c_617, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_614])).
% 6.99/2.52  tff(c_654, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k4_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_556, c_642])).
% 6.99/2.52  tff(c_663, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_617, c_654])).
% 6.99/2.52  tff(c_1624, plain, (![A_118, B_119]: (k5_xboole_0(k5_xboole_0(A_118, B_119), k2_xboole_0(A_118, B_119))=k3_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.99/2.52  tff(c_1658, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_11, A_11))=k3_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_663, c_1624])).
% 6.99/2.52  tff(c_1667, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_11, A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_556, c_1658])).
% 6.99/2.52  tff(c_2166, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_2138, c_1667])).
% 6.99/2.52  tff(c_669, plain, (![A_74]: (k3_xboole_0(k1_xboole_0, A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_665, c_6])).
% 6.99/2.52  tff(c_541, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 6.99/2.52  tff(c_555, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_541, c_542])).
% 6.99/2.52  tff(c_657, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_555, c_642])).
% 6.99/2.52  tff(c_820, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_663, c_657])).
% 6.99/2.52  tff(c_558, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_542])).
% 6.99/2.52  tff(c_651, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_558, c_642])).
% 6.99/2.52  tff(c_1259, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_663, c_651])).
% 6.99/2.52  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k2_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.99/2.52  tff(c_10194, plain, (![A_262, B_263, C_264]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_262, B_263), k3_xboole_0(A_262, C_264)), k4_xboole_0(A_262, k4_xboole_0(B_263, C_264)))=k3_xboole_0(k4_xboole_0(A_262, B_263), k3_xboole_0(A_262, C_264)))), inference(superposition, [status(thm), theory('equality')], [c_2046, c_24])).
% 6.99/2.52  tff(c_10380, plain, (k5_xboole_0(k5_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3')), k1_xboole_0)=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1259, c_10194])).
% 6.99/2.52  tff(c_10484, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2166, c_669, c_820, c_664, c_820, c_10380])).
% 6.99/2.52  tff(c_1039, plain, (![A_98, B_99, C_100]: (k5_xboole_0(k5_xboole_0(A_98, B_99), C_100)=k5_xboole_0(A_98, k5_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.99/2.52  tff(c_4370, plain, (![A_178, B_179, C_180]: (k5_xboole_0(A_178, k5_xboole_0(k3_xboole_0(A_178, B_179), C_180))=k5_xboole_0(k4_xboole_0(A_178, B_179), C_180))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1039])).
% 6.99/2.52  tff(c_4479, plain, (![A_178, B_179]: (k5_xboole_0(k4_xboole_0(A_178, B_179), k3_xboole_0(A_178, B_179))=k5_xboole_0(A_178, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_663, c_4370])).
% 6.99/2.52  tff(c_4606, plain, (![A_183, B_184]: (k5_xboole_0(k4_xboole_0(A_183, B_184), k3_xboole_0(A_183, B_184))=A_183)), inference(demodulation, [status(thm), theory('equality')], [c_664, c_4479])).
% 6.99/2.52  tff(c_1070, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k5_xboole_0(B_99, k5_xboole_0(A_98, B_99)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_663, c_1039])).
% 6.99/2.52  tff(c_1066, plain, (![A_11, C_100]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_100))=k5_xboole_0(k1_xboole_0, C_100))), inference(superposition, [status(thm), theory('equality')], [c_663, c_1039])).
% 6.99/2.52  tff(c_3475, plain, (![A_158, C_159]: (k5_xboole_0(A_158, k5_xboole_0(A_158, C_159))=C_159)), inference(demodulation, [status(thm), theory('equality')], [c_2166, c_1066])).
% 6.99/2.52  tff(c_3519, plain, (![B_99, A_98]: (k5_xboole_0(B_99, k5_xboole_0(A_98, B_99))=k5_xboole_0(A_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1070, c_3475])).
% 6.99/2.52  tff(c_3568, plain, (![B_99, A_98]: (k5_xboole_0(B_99, k5_xboole_0(A_98, B_99))=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_664, c_3519])).
% 6.99/2.52  tff(c_4624, plain, (![A_183, B_184]: (k5_xboole_0(k3_xboole_0(A_183, B_184), A_183)=k4_xboole_0(A_183, B_184))), inference(superposition, [status(thm), theory('equality')], [c_4606, c_3568])).
% 6.99/2.52  tff(c_10518, plain, (k5_xboole_0(k1_xboole_0, '#skF_1')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10484, c_4624])).
% 6.99/2.52  tff(c_10588, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2166, c_10518])).
% 6.99/2.52  tff(c_10590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_10588])).
% 6.99/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.99/2.52  
% 6.99/2.52  Inference rules
% 6.99/2.52  ----------------------
% 6.99/2.52  #Ref     : 0
% 6.99/2.52  #Sup     : 2651
% 6.99/2.52  #Fact    : 0
% 6.99/2.52  #Define  : 0
% 6.99/2.52  #Split   : 2
% 6.99/2.52  #Chain   : 0
% 6.99/2.52  #Close   : 0
% 6.99/2.52  
% 6.99/2.52  Ordering : KBO
% 6.99/2.52  
% 6.99/2.52  Simplification rules
% 6.99/2.52  ----------------------
% 6.99/2.52  #Subsume      : 75
% 6.99/2.52  #Demod        : 3179
% 6.99/2.52  #Tautology    : 1709
% 6.99/2.52  #SimpNegUnit  : 2
% 6.99/2.52  #BackRed      : 24
% 6.99/2.52  
% 6.99/2.52  #Partial instantiations: 0
% 6.99/2.52  #Strategies tried      : 1
% 6.99/2.52  
% 6.99/2.52  Timing (in seconds)
% 6.99/2.52  ----------------------
% 6.99/2.52  Preprocessing        : 0.28
% 6.99/2.52  Parsing              : 0.16
% 6.99/2.52  CNF conversion       : 0.02
% 6.99/2.52  Main loop            : 1.47
% 6.99/2.52  Inferencing          : 0.42
% 6.99/2.52  Reduction            : 0.72
% 6.99/2.52  Demodulation         : 0.61
% 6.99/2.52  BG Simplification    : 0.05
% 6.99/2.52  Subsumption          : 0.20
% 6.99/2.52  Abstraction          : 0.08
% 6.99/2.52  MUC search           : 0.00
% 6.99/2.52  Cooper               : 0.00
% 6.99/2.52  Total                : 1.79
% 6.99/2.52  Index Insertion      : 0.00
% 6.99/2.52  Index Deletion       : 0.00
% 6.99/2.52  Index Matching       : 0.00
% 6.99/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
