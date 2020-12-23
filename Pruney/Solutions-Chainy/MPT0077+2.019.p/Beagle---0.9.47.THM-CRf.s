%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:37 EST 2020

% Result     : Theorem 12.72s
% Output     : CNFRefutation 12.72s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 694 expanded)
%              Number of leaves         :   23 ( 238 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 (1008 expanded)
%              Number of equality atoms :  124 ( 528 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_287,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_291,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_287])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_142,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_149,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_31,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_292,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_296,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_292,c_4])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_103,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_107,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_16])).

tff(c_114,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_401,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k4_xboole_0(A_38,B_39),C_40) = k4_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_579,plain,(
    ! [C_45] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_45)) = k4_xboole_0('#skF_4',C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_401])).

tff(c_598,plain,(
    ! [C_45] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_45)) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_18])).

tff(c_627,plain,(
    ! [C_45] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_45)) = k3_xboole_0('#skF_4',C_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_598])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_28])).

tff(c_354,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_358,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_354])).

tff(c_3786,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_358])).

tff(c_3789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_3786])).

tff(c_3790,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_3795,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3790,c_4])).

tff(c_3806,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3795,c_16])).

tff(c_3810,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3806])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3836,plain,(
    ! [A_94,B_95,C_96] : k4_xboole_0(k4_xboole_0(A_94,B_95),C_96) = k4_xboole_0(A_94,k2_xboole_0(B_95,C_96)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3849,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k2_xboole_0(B_95,k4_xboole_0(A_94,B_95))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3836,c_149])).

tff(c_3919,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k2_xboole_0(B_98,A_97)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3849])).

tff(c_3958,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3919])).

tff(c_3890,plain,(
    ! [A_94,B_95,B_15] : k4_xboole_0(A_94,k2_xboole_0(B_95,k4_xboole_0(k4_xboole_0(A_94,B_95),B_15))) = k3_xboole_0(k4_xboole_0(A_94,B_95),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3836])).

tff(c_10032,plain,(
    ! [A_181,B_182,B_183] : k4_xboole_0(A_181,k2_xboole_0(B_182,k4_xboole_0(A_181,k2_xboole_0(B_182,B_183)))) = k3_xboole_0(k4_xboole_0(A_181,B_182),B_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3890])).

tff(c_10308,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_1')) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3810,c_10032])).

tff(c_10400,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3958,c_2,c_10308])).

tff(c_10634,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k1_xboole_0) = k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10400,c_16])).

tff(c_10641,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3810,c_14,c_12,c_10634])).

tff(c_10841,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10641,c_10400])).

tff(c_10844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_10841])).

tff(c_10845,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_10854,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10845,c_4])).

tff(c_10858,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10854,c_16])).

tff(c_10861,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10858])).

tff(c_10993,plain,(
    ! [C_11] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_11)) = k4_xboole_0('#skF_1',C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_10861,c_14])).

tff(c_10863,plain,(
    ! [A_187,B_188,C_189] : k4_xboole_0(k4_xboole_0(A_187,B_188),C_189) = k4_xboole_0(A_187,k2_xboole_0(B_188,C_189)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10866,plain,(
    ! [A_187,B_188,C_189,C_11] : k4_xboole_0(k4_xboole_0(A_187,k2_xboole_0(B_188,C_189)),C_11) = k4_xboole_0(k4_xboole_0(A_187,B_188),k2_xboole_0(C_189,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10863,c_14])).

tff(c_17611,plain,(
    ! [A_279,B_280,C_281,C_282] : k4_xboole_0(A_279,k2_xboole_0(k2_xboole_0(B_280,C_281),C_282)) = k4_xboole_0(A_279,k2_xboole_0(B_280,k2_xboole_0(C_281,C_282))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_10866])).

tff(c_17894,plain,(
    ! [C_11] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_11))) = k4_xboole_0('#skF_1',C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_10993,c_17611])).

tff(c_195,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_204,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_195])).

tff(c_18529,plain,(
    ! [C_289] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_289))) = k4_xboole_0('#skF_1',C_289) ),
    inference(superposition,[status(thm),theory(equality)],[c_10993,c_17611])).

tff(c_18613,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_2'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_18529])).

tff(c_18648,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17894,c_12,c_18613])).

tff(c_18686,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18648,c_18])).

tff(c_18699,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_18686])).

tff(c_18701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_18699])).

tff(c_18702,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_18728,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18702])).

tff(c_18732,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_18728])).

tff(c_18703,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_18707,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18703,c_4])).

tff(c_18711,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18707,c_16])).

tff(c_18714,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18711])).

tff(c_29870,plain,(
    ! [A_424,B_425,C_426] : k4_xboole_0(k4_xboole_0(A_424,B_425),C_426) = k4_xboole_0(A_424,k2_xboole_0(B_425,C_426)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30209,plain,(
    ! [C_436] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_436)) = k4_xboole_0('#skF_1',C_436) ),
    inference(superposition,[status(thm),theory(equality)],[c_18714,c_29870])).

tff(c_30842,plain,(
    ! [B_447] : k4_xboole_0('#skF_1',k2_xboole_0(B_447,'#skF_2')) = k4_xboole_0('#skF_1',B_447) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_30209])).

tff(c_18800,plain,(
    ! [A_292,B_293,C_294] : k4_xboole_0(k4_xboole_0(A_292,B_293),C_294) = k4_xboole_0(A_292,k2_xboole_0(B_293,C_294)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28839,plain,(
    ! [C_407] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_407)) = k4_xboole_0('#skF_1',C_407) ),
    inference(superposition,[status(thm),theory(equality)],[c_18714,c_18800])).

tff(c_29756,plain,(
    ! [B_423] : k4_xboole_0('#skF_1',k2_xboole_0(B_423,'#skF_2')) = k4_xboole_0('#skF_1',B_423) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_28839])).

tff(c_18733,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_18737,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18733,c_4])).

tff(c_27604,plain,(
    ! [A_397,B_398,C_399] : k4_xboole_0(k4_xboole_0(A_397,B_398),k4_xboole_0(A_397,k2_xboole_0(B_398,C_399))) = k3_xboole_0(k4_xboole_0(A_397,B_398),C_399) ),
    inference(superposition,[status(thm),theory(equality)],[c_18800,c_18])).

tff(c_27909,plain,(
    ! [C_399] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_399))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_399) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_27604])).

tff(c_28008,plain,(
    ! [C_399] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_399)) = k3_xboole_0('#skF_4',C_399) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_18,c_27909])).

tff(c_18976,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_18980,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_18976])).

tff(c_28733,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28008,c_18980])).

tff(c_28736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18737,c_28733])).

tff(c_28737,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_28742,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28737,c_4])).

tff(c_28750,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28742,c_16])).

tff(c_28753,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28750])).

tff(c_29774,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_29756,c_28753])).

tff(c_29844,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29774,c_18])).

tff(c_29849,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_29844])).

tff(c_29851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18732,c_29849])).

tff(c_29852,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_29861,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29852,c_4])).

tff(c_29865,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_29861,c_16])).

tff(c_29868,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_29865])).

tff(c_30860,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_30842,c_29868])).

tff(c_30923,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30860,c_18])).

tff(c_30927,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_30923])).

tff(c_30929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18732,c_30927])).

tff(c_30930,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_18702])).

tff(c_30935,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30930,c_4])).

tff(c_31080,plain,(
    ! [A_452,B_453,C_454] : k4_xboole_0(k4_xboole_0(A_452,B_453),C_454) = k4_xboole_0(A_452,k2_xboole_0(B_453,C_454)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_41242,plain,(
    ! [A_569,B_570,C_571] : k4_xboole_0(k4_xboole_0(A_569,B_570),k4_xboole_0(A_569,k2_xboole_0(B_570,C_571))) = k3_xboole_0(k4_xboole_0(A_569,B_570),C_571) ),
    inference(superposition,[status(thm),theory(equality)],[c_31080,c_18])).

tff(c_41611,plain,(
    ! [C_571] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_571))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_571) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_41242])).

tff(c_41738,plain,(
    ! [C_571] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_571)) = k3_xboole_0('#skF_4',C_571) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_18,c_41611])).

tff(c_30981,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_30985,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_30981])).

tff(c_43657,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41738,c_30985])).

tff(c_43660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30935,c_43657])).

tff(c_43662,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_30931,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18702])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_43823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43662,c_18703,c_30931,c_32])).

tff(c_43825,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_43920,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_43825,c_22])).

tff(c_43921,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_43920])).

tff(c_43925,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_43921])).

tff(c_43846,plain,(
    ! [A_589,B_590] : k4_xboole_0(A_589,k4_xboole_0(A_589,B_590)) = k3_xboole_0(A_589,B_590) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43867,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_43846])).

tff(c_43874,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43867])).

tff(c_43824,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_43833,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43824,c_4])).

tff(c_43837,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_43833,c_16])).

tff(c_43840,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_43837])).

tff(c_44091,plain,(
    ! [A_601,B_602,C_603] : k4_xboole_0(k4_xboole_0(A_601,B_602),C_603) = k4_xboole_0(A_601,k2_xboole_0(B_602,C_603)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44145,plain,(
    ! [C_603] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_603)) = k4_xboole_0('#skF_1',C_603) ),
    inference(superposition,[status(thm),theory(equality)],[c_43840,c_44091])).

tff(c_44125,plain,(
    ! [A_9,B_10,C_11,C_603] : k4_xboole_0(k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)),C_603) = k4_xboole_0(k4_xboole_0(A_9,B_10),k2_xboole_0(C_11,C_603)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_44091])).

tff(c_49908,plain,(
    ! [A_678,B_679,C_680,C_681] : k4_xboole_0(A_678,k2_xboole_0(k2_xboole_0(B_679,C_680),C_681)) = k4_xboole_0(A_678,k2_xboole_0(B_679,k2_xboole_0(C_680,C_681))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_44125])).

tff(c_50176,plain,(
    ! [C_603] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_603))) = k4_xboole_0('#skF_1',C_603) ),
    inference(superposition,[status(thm),theory(equality)],[c_44145,c_49908])).

tff(c_43927,plain,(
    ! [A_593,B_594] : k2_xboole_0(A_593,k4_xboole_0(B_594,A_593)) = k2_xboole_0(A_593,B_594) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43936,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_43874,c_43927])).

tff(c_50761,plain,(
    ! [C_688] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_688))) = k4_xboole_0('#skF_1',C_688) ),
    inference(superposition,[status(thm),theory(equality)],[c_44145,c_49908])).

tff(c_50840,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_2'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_43936,c_50761])).

tff(c_50870,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50176,c_12,c_50840])).

tff(c_50911,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50870,c_18])).

tff(c_50925,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43874,c_50911])).

tff(c_50927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43925,c_50925])).

tff(c_50928,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_43920])).

tff(c_50933,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_50928])).

tff(c_50929,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_43920])).

tff(c_50937,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50929,c_4])).

tff(c_50941,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50937,c_16])).

tff(c_50944,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50941])).

tff(c_51136,plain,(
    ! [A_697,B_698,C_699] : k4_xboole_0(k4_xboole_0(A_697,B_698),C_699) = k4_xboole_0(A_697,k2_xboole_0(B_698,C_699)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51587,plain,(
    ! [C_709] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_709)) = k4_xboole_0('#skF_1',C_709) ),
    inference(superposition,[status(thm),theory(equality)],[c_50944,c_51136])).

tff(c_52231,plain,(
    ! [A_719] : k4_xboole_0('#skF_1',k2_xboole_0(A_719,'#skF_2')) = k4_xboole_0('#skF_1',A_719) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51587])).

tff(c_52265,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_52231,c_43840])).

tff(c_52329,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_52265,c_18])).

tff(c_52334,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43874,c_52329])).

tff(c_52336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50933,c_52334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.72/6.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.72/6.26  
% 12.72/6.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.72/6.26  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.72/6.26  
% 12.72/6.26  %Foreground sorts:
% 12.72/6.26  
% 12.72/6.26  
% 12.72/6.26  %Background operators:
% 12.72/6.26  
% 12.72/6.26  
% 12.72/6.26  %Foreground operators:
% 12.72/6.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.72/6.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.72/6.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.72/6.26  tff('#skF_5', type, '#skF_5': $i).
% 12.72/6.26  tff('#skF_6', type, '#skF_6': $i).
% 12.72/6.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.72/6.26  tff('#skF_2', type, '#skF_2': $i).
% 12.72/6.26  tff('#skF_3', type, '#skF_3': $i).
% 12.72/6.26  tff('#skF_1', type, '#skF_1': $i).
% 12.72/6.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.72/6.26  tff('#skF_4', type, '#skF_4': $i).
% 12.72/6.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.72/6.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.72/6.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.72/6.26  
% 12.72/6.29  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.72/6.29  tff(f_60, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 12.72/6.29  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 12.72/6.29  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.72/6.29  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.72/6.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.72/6.29  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 12.72/6.29  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.72/6.29  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.72/6.29  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.72/6.29  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.72/6.29  tff(c_287, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 12.72/6.29  tff(c_291, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_287])).
% 12.72/6.29  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.72/6.29  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.72/6.29  tff(c_121, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.72/6.29  tff(c_142, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_121])).
% 12.72/6.29  tff(c_149, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_142])).
% 12.72/6.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.72/6.29  tff(c_24, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.72/6.29  tff(c_31, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 12.72/6.29  tff(c_292, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_31])).
% 12.72/6.29  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.72/6.29  tff(c_296, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_292, c_4])).
% 12.72/6.29  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.72/6.29  tff(c_20, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.72/6.29  tff(c_34, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 12.72/6.29  tff(c_103, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 12.72/6.29  tff(c_107, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_103, c_4])).
% 12.72/6.29  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.72/6.29  tff(c_111, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_107, c_16])).
% 12.72/6.29  tff(c_114, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_111])).
% 12.72/6.29  tff(c_401, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k4_xboole_0(A_38, B_39), C_40)=k4_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_579, plain, (![C_45]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_45))=k4_xboole_0('#skF_4', C_45))), inference(superposition, [status(thm), theory('equality')], [c_114, c_401])).
% 12.72/6.29  tff(c_598, plain, (![C_45]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_45))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_45)))), inference(superposition, [status(thm), theory('equality')], [c_579, c_18])).
% 12.72/6.29  tff(c_627, plain, (![C_45]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_45))=k3_xboole_0('#skF_4', C_45))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_598])).
% 12.72/6.29  tff(c_28, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.72/6.29  tff(c_33, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_28])).
% 12.72/6.29  tff(c_354, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 12.72/6.29  tff(c_358, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_354])).
% 12.72/6.29  tff(c_3786, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_627, c_358])).
% 12.72/6.29  tff(c_3789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_296, c_3786])).
% 12.72/6.29  tff(c_3790, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 12.72/6.29  tff(c_3795, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3790, c_4])).
% 12.72/6.29  tff(c_3806, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3795, c_16])).
% 12.72/6.29  tff(c_3810, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3806])).
% 12.72/6.29  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.72/6.29  tff(c_3836, plain, (![A_94, B_95, C_96]: (k4_xboole_0(k4_xboole_0(A_94, B_95), C_96)=k4_xboole_0(A_94, k2_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_3849, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k2_xboole_0(B_95, k4_xboole_0(A_94, B_95)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3836, c_149])).
% 12.72/6.29  tff(c_3919, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k2_xboole_0(B_98, A_97))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3849])).
% 12.72/6.29  tff(c_3958, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3919])).
% 12.72/6.29  tff(c_3890, plain, (![A_94, B_95, B_15]: (k4_xboole_0(A_94, k2_xboole_0(B_95, k4_xboole_0(k4_xboole_0(A_94, B_95), B_15)))=k3_xboole_0(k4_xboole_0(A_94, B_95), B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3836])).
% 12.72/6.29  tff(c_10032, plain, (![A_181, B_182, B_183]: (k4_xboole_0(A_181, k2_xboole_0(B_182, k4_xboole_0(A_181, k2_xboole_0(B_182, B_183))))=k3_xboole_0(k4_xboole_0(A_181, B_182), B_183))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3890])).
% 12.72/6.29  tff(c_10308, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3810, c_10032])).
% 12.72/6.29  tff(c_10400, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3958, c_2, c_10308])).
% 12.72/6.29  tff(c_10634, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)=k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10400, c_16])).
% 12.72/6.29  tff(c_10641, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3810, c_14, c_12, c_10634])).
% 12.72/6.29  tff(c_10841, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10641, c_10400])).
% 12.72/6.29  tff(c_10844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_10841])).
% 12.72/6.29  tff(c_10845, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 12.72/6.29  tff(c_10854, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10845, c_4])).
% 12.72/6.29  tff(c_10858, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10854, c_16])).
% 12.72/6.29  tff(c_10861, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10858])).
% 12.72/6.29  tff(c_10993, plain, (![C_11]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_11))=k4_xboole_0('#skF_1', C_11))), inference(superposition, [status(thm), theory('equality')], [c_10861, c_14])).
% 12.72/6.29  tff(c_10863, plain, (![A_187, B_188, C_189]: (k4_xboole_0(k4_xboole_0(A_187, B_188), C_189)=k4_xboole_0(A_187, k2_xboole_0(B_188, C_189)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_10866, plain, (![A_187, B_188, C_189, C_11]: (k4_xboole_0(k4_xboole_0(A_187, k2_xboole_0(B_188, C_189)), C_11)=k4_xboole_0(k4_xboole_0(A_187, B_188), k2_xboole_0(C_189, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_10863, c_14])).
% 12.72/6.29  tff(c_17611, plain, (![A_279, B_280, C_281, C_282]: (k4_xboole_0(A_279, k2_xboole_0(k2_xboole_0(B_280, C_281), C_282))=k4_xboole_0(A_279, k2_xboole_0(B_280, k2_xboole_0(C_281, C_282))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_10866])).
% 12.72/6.29  tff(c_17894, plain, (![C_11]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_11)))=k4_xboole_0('#skF_1', C_11))), inference(superposition, [status(thm), theory('equality')], [c_10993, c_17611])).
% 12.72/6.29  tff(c_195, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.72/6.29  tff(c_204, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_149, c_195])).
% 12.72/6.29  tff(c_18529, plain, (![C_289]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_289)))=k4_xboole_0('#skF_1', C_289))), inference(superposition, [status(thm), theory('equality')], [c_10993, c_17611])).
% 12.72/6.29  tff(c_18613, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_2')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_204, c_18529])).
% 12.72/6.29  tff(c_18648, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17894, c_12, c_18613])).
% 12.72/6.29  tff(c_18686, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18648, c_18])).
% 12.72/6.29  tff(c_18699, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_149, c_18686])).
% 12.72/6.29  tff(c_18701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_18699])).
% 12.72/6.29  tff(c_18702, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 12.72/6.29  tff(c_18728, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_18702])).
% 12.72/6.29  tff(c_18732, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_18728])).
% 12.72/6.29  tff(c_18703, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 12.72/6.29  tff(c_18707, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18703, c_4])).
% 12.72/6.29  tff(c_18711, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18707, c_16])).
% 12.72/6.29  tff(c_18714, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18711])).
% 12.72/6.29  tff(c_29870, plain, (![A_424, B_425, C_426]: (k4_xboole_0(k4_xboole_0(A_424, B_425), C_426)=k4_xboole_0(A_424, k2_xboole_0(B_425, C_426)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_30209, plain, (![C_436]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_436))=k4_xboole_0('#skF_1', C_436))), inference(superposition, [status(thm), theory('equality')], [c_18714, c_29870])).
% 12.72/6.29  tff(c_30842, plain, (![B_447]: (k4_xboole_0('#skF_1', k2_xboole_0(B_447, '#skF_2'))=k4_xboole_0('#skF_1', B_447))), inference(superposition, [status(thm), theory('equality')], [c_2, c_30209])).
% 12.72/6.29  tff(c_18800, plain, (![A_292, B_293, C_294]: (k4_xboole_0(k4_xboole_0(A_292, B_293), C_294)=k4_xboole_0(A_292, k2_xboole_0(B_293, C_294)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_28839, plain, (![C_407]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_407))=k4_xboole_0('#skF_1', C_407))), inference(superposition, [status(thm), theory('equality')], [c_18714, c_18800])).
% 12.72/6.29  tff(c_29756, plain, (![B_423]: (k4_xboole_0('#skF_1', k2_xboole_0(B_423, '#skF_2'))=k4_xboole_0('#skF_1', B_423))), inference(superposition, [status(thm), theory('equality')], [c_2, c_28839])).
% 12.72/6.29  tff(c_18733, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_31])).
% 12.72/6.29  tff(c_18737, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_18733, c_4])).
% 12.72/6.29  tff(c_27604, plain, (![A_397, B_398, C_399]: (k4_xboole_0(k4_xboole_0(A_397, B_398), k4_xboole_0(A_397, k2_xboole_0(B_398, C_399)))=k3_xboole_0(k4_xboole_0(A_397, B_398), C_399))), inference(superposition, [status(thm), theory('equality')], [c_18800, c_18])).
% 12.72/6.29  tff(c_27909, plain, (![C_399]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_399)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_399))), inference(superposition, [status(thm), theory('equality')], [c_114, c_27604])).
% 12.72/6.29  tff(c_28008, plain, (![C_399]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_399))=k3_xboole_0('#skF_4', C_399))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_18, c_27909])).
% 12.72/6.29  tff(c_18976, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 12.72/6.29  tff(c_18980, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_18976])).
% 12.72/6.29  tff(c_28733, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28008, c_18980])).
% 12.72/6.29  tff(c_28736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18737, c_28733])).
% 12.72/6.29  tff(c_28737, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 12.72/6.29  tff(c_28742, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28737, c_4])).
% 12.72/6.29  tff(c_28750, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28742, c_16])).
% 12.72/6.29  tff(c_28753, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28750])).
% 12.72/6.29  tff(c_29774, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_29756, c_28753])).
% 12.72/6.29  tff(c_29844, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29774, c_18])).
% 12.72/6.29  tff(c_29849, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_149, c_29844])).
% 12.72/6.29  tff(c_29851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18732, c_29849])).
% 12.72/6.29  tff(c_29852, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 12.72/6.29  tff(c_29861, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29852, c_4])).
% 12.72/6.29  tff(c_29865, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_29861, c_16])).
% 12.72/6.29  tff(c_29868, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_29865])).
% 12.72/6.29  tff(c_30860, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_30842, c_29868])).
% 12.72/6.29  tff(c_30923, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30860, c_18])).
% 12.72/6.29  tff(c_30927, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_149, c_30923])).
% 12.72/6.29  tff(c_30929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18732, c_30927])).
% 12.72/6.29  tff(c_30930, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_18702])).
% 12.72/6.29  tff(c_30935, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30930, c_4])).
% 12.72/6.29  tff(c_31080, plain, (![A_452, B_453, C_454]: (k4_xboole_0(k4_xboole_0(A_452, B_453), C_454)=k4_xboole_0(A_452, k2_xboole_0(B_453, C_454)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_41242, plain, (![A_569, B_570, C_571]: (k4_xboole_0(k4_xboole_0(A_569, B_570), k4_xboole_0(A_569, k2_xboole_0(B_570, C_571)))=k3_xboole_0(k4_xboole_0(A_569, B_570), C_571))), inference(superposition, [status(thm), theory('equality')], [c_31080, c_18])).
% 12.72/6.29  tff(c_41611, plain, (![C_571]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_571)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_571))), inference(superposition, [status(thm), theory('equality')], [c_114, c_41242])).
% 12.72/6.29  tff(c_41738, plain, (![C_571]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_571))=k3_xboole_0('#skF_4', C_571))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_18, c_41611])).
% 12.72/6.29  tff(c_30981, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 12.72/6.29  tff(c_30985, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_30981])).
% 12.72/6.29  tff(c_43657, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_41738, c_30985])).
% 12.72/6.29  tff(c_43660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30935, c_43657])).
% 12.72/6.29  tff(c_43662, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_33])).
% 12.72/6.29  tff(c_30931, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18702])).
% 12.72/6.29  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.72/6.29  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 12.72/6.29  tff(c_43823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43662, c_18703, c_30931, c_32])).
% 12.72/6.29  tff(c_43825, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 12.72/6.29  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.72/6.29  tff(c_43920, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_43825, c_22])).
% 12.72/6.29  tff(c_43921, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_43920])).
% 12.72/6.29  tff(c_43925, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_43921])).
% 12.72/6.29  tff(c_43846, plain, (![A_589, B_590]: (k4_xboole_0(A_589, k4_xboole_0(A_589, B_590))=k3_xboole_0(A_589, B_590))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.72/6.29  tff(c_43867, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_43846])).
% 12.72/6.29  tff(c_43874, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_43867])).
% 12.72/6.29  tff(c_43824, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 12.72/6.29  tff(c_43833, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_43824, c_4])).
% 12.72/6.29  tff(c_43837, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_43833, c_16])).
% 12.72/6.29  tff(c_43840, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_43837])).
% 12.72/6.29  tff(c_44091, plain, (![A_601, B_602, C_603]: (k4_xboole_0(k4_xboole_0(A_601, B_602), C_603)=k4_xboole_0(A_601, k2_xboole_0(B_602, C_603)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_44145, plain, (![C_603]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_603))=k4_xboole_0('#skF_1', C_603))), inference(superposition, [status(thm), theory('equality')], [c_43840, c_44091])).
% 12.72/6.29  tff(c_44125, plain, (![A_9, B_10, C_11, C_603]: (k4_xboole_0(k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)), C_603)=k4_xboole_0(k4_xboole_0(A_9, B_10), k2_xboole_0(C_11, C_603)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_44091])).
% 12.72/6.29  tff(c_49908, plain, (![A_678, B_679, C_680, C_681]: (k4_xboole_0(A_678, k2_xboole_0(k2_xboole_0(B_679, C_680), C_681))=k4_xboole_0(A_678, k2_xboole_0(B_679, k2_xboole_0(C_680, C_681))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_44125])).
% 12.72/6.29  tff(c_50176, plain, (![C_603]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_603)))=k4_xboole_0('#skF_1', C_603))), inference(superposition, [status(thm), theory('equality')], [c_44145, c_49908])).
% 12.72/6.29  tff(c_43927, plain, (![A_593, B_594]: (k2_xboole_0(A_593, k4_xboole_0(B_594, A_593))=k2_xboole_0(A_593, B_594))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.72/6.29  tff(c_43936, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_43874, c_43927])).
% 12.72/6.29  tff(c_50761, plain, (![C_688]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_688)))=k4_xboole_0('#skF_1', C_688))), inference(superposition, [status(thm), theory('equality')], [c_44145, c_49908])).
% 12.72/6.29  tff(c_50840, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_2')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_43936, c_50761])).
% 12.72/6.29  tff(c_50870, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50176, c_12, c_50840])).
% 12.72/6.29  tff(c_50911, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50870, c_18])).
% 12.72/6.29  tff(c_50925, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_43874, c_50911])).
% 12.72/6.29  tff(c_50927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43925, c_50925])).
% 12.72/6.29  tff(c_50928, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_43920])).
% 12.72/6.29  tff(c_50933, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_50928])).
% 12.72/6.29  tff(c_50929, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_43920])).
% 12.72/6.29  tff(c_50937, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_50929, c_4])).
% 12.72/6.29  tff(c_50941, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50937, c_16])).
% 12.72/6.29  tff(c_50944, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50941])).
% 12.72/6.29  tff(c_51136, plain, (![A_697, B_698, C_699]: (k4_xboole_0(k4_xboole_0(A_697, B_698), C_699)=k4_xboole_0(A_697, k2_xboole_0(B_698, C_699)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/6.29  tff(c_51587, plain, (![C_709]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_709))=k4_xboole_0('#skF_1', C_709))), inference(superposition, [status(thm), theory('equality')], [c_50944, c_51136])).
% 12.72/6.29  tff(c_52231, plain, (![A_719]: (k4_xboole_0('#skF_1', k2_xboole_0(A_719, '#skF_2'))=k4_xboole_0('#skF_1', A_719))), inference(superposition, [status(thm), theory('equality')], [c_2, c_51587])).
% 12.72/6.29  tff(c_52265, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_52231, c_43840])).
% 12.72/6.29  tff(c_52329, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_52265, c_18])).
% 12.72/6.29  tff(c_52334, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_43874, c_52329])).
% 12.72/6.29  tff(c_52336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50933, c_52334])).
% 12.72/6.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.72/6.29  
% 12.72/6.29  Inference rules
% 12.72/6.29  ----------------------
% 12.72/6.29  #Ref     : 0
% 12.72/6.29  #Sup     : 12525
% 12.72/6.29  #Fact    : 0
% 12.72/6.29  #Define  : 0
% 12.72/6.29  #Split   : 9
% 12.72/6.29  #Chain   : 0
% 12.72/6.29  #Close   : 0
% 12.72/6.29  
% 12.72/6.29  Ordering : KBO
% 12.72/6.29  
% 12.72/6.29  Simplification rules
% 12.72/6.29  ----------------------
% 12.72/6.29  #Subsume      : 154
% 12.72/6.29  #Demod        : 14376
% 12.72/6.29  #Tautology    : 7945
% 12.72/6.29  #SimpNegUnit  : 7
% 12.72/6.29  #BackRed      : 18
% 12.72/6.29  
% 12.72/6.29  #Partial instantiations: 0
% 12.72/6.29  #Strategies tried      : 1
% 12.72/6.29  
% 12.72/6.29  Timing (in seconds)
% 12.72/6.29  ----------------------
% 12.72/6.29  Preprocessing        : 0.27
% 12.72/6.29  Parsing              : 0.15
% 12.72/6.29  CNF conversion       : 0.02
% 12.72/6.29  Main loop            : 5.22
% 12.72/6.29  Inferencing          : 1.05
% 12.72/6.29  Reduction            : 3.15
% 12.72/6.29  Demodulation         : 2.82
% 12.72/6.29  BG Simplification    : 0.14
% 12.72/6.29  Subsumption          : 0.66
% 12.72/6.29  Abstraction          : 0.23
% 12.72/6.29  MUC search           : 0.00
% 12.72/6.29  Cooper               : 0.00
% 12.72/6.29  Total                : 5.55
% 12.72/6.29  Index Insertion      : 0.00
% 12.72/6.29  Index Deletion       : 0.00
% 12.72/6.29  Index Matching       : 0.00
% 12.72/6.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
