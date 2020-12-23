%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:25 EST 2020

% Result     : Theorem 8.18s
% Output     : CNFRefutation 8.36s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 192 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 320 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k5_xboole_0(B,C))
      <=> ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(c_38,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8258,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,(
    ! [A_32,B_33] : k2_xboole_0(k5_xboole_0(A_32,B_33),k3_xboole_0(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_xboole_0(k3_xboole_0(A_3,B_4),k5_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_141,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    k2_xboole_0('#skF_4',k5_xboole_0('#skF_5','#skF_6')) = k5_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_141,c_8])).

tff(c_28,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_xboole_0(A_27,B_28)
      | ~ r1_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_216,plain,(
    ! [A_65] :
      ( r1_xboole_0(A_65,'#skF_4')
      | ~ r1_xboole_0(A_65,k5_xboole_0('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_28])).

tff(c_226,plain,(
    r1_xboole_0(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_216])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_240,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_265,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_36])).

tff(c_266,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_149,plain,(
    k3_xboole_0('#skF_4',k5_xboole_0('#skF_5','#skF_6')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_141,c_12])).

tff(c_475,plain,(
    ! [A_86,B_87,C_88] : r1_tarski(k2_xboole_0(k3_xboole_0(A_86,B_87),k3_xboole_0(A_86,C_88)),k2_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_493,plain,(
    ! [C_88] : r1_tarski(k2_xboole_0('#skF_4',k3_xboole_0('#skF_4',C_88)),k2_xboole_0(k5_xboole_0('#skF_5','#skF_6'),C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_475])).

tff(c_503,plain,(
    ! [C_89] : r1_tarski('#skF_4',k2_xboole_0(k5_xboole_0('#skF_5','#skF_6'),C_89)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_493])).

tff(c_513,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_503])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_513])).

tff(c_523,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_540,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_240,c_38])).

tff(c_522,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_18,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(k2_xboole_0(A_30,B_31),B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_45,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30])).

tff(c_529,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_522,c_45])).

tff(c_728,plain,(
    ! [A_93,B_94] : k4_xboole_0(k2_xboole_0(A_93,B_94),k3_xboole_0(A_93,B_94)) = k5_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(k4_xboole_0(A_16,C_18),k4_xboole_0(B_17,C_18))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7295,plain,(
    ! [A_256,A_257,B_258] :
      ( r1_tarski(k4_xboole_0(A_256,k3_xboole_0(A_257,B_258)),k5_xboole_0(A_257,B_258))
      | ~ r1_tarski(A_256,k2_xboole_0(A_257,B_258)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_16])).

tff(c_7376,plain,
    ( r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_7295])).

tff(c_7410,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_7376])).

tff(c_7412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_7410])).

tff(c_7413,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7414,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7445,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_7414,c_42])).

tff(c_7451,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7445,c_45])).

tff(c_7628,plain,(
    ! [A_268,C_269,B_270] :
      ( r1_tarski(k4_xboole_0(A_268,C_269),k4_xboole_0(B_270,C_269))
      | ~ r1_tarski(A_268,B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8069,plain,(
    ! [B_304] :
      ( r1_tarski('#skF_1',k4_xboole_0(B_304,k3_xboole_0('#skF_2','#skF_3')))
      | ~ r1_tarski('#skF_1',B_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7451,c_7628])).

tff(c_8083,plain,
    ( r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_8069])).

tff(c_8099,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7413,c_8083])).

tff(c_8101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_8099])).

tff(c_8102,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_8111,plain,(
    k3_xboole_0('#skF_4',k5_xboole_0('#skF_5','#skF_6')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8102,c_12])).

tff(c_8769,plain,(
    ! [A_343,B_344,C_345] : r1_tarski(k2_xboole_0(k3_xboole_0(A_343,B_344),k3_xboole_0(A_343,C_345)),k2_xboole_0(B_344,C_345)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8799,plain,(
    ! [C_345] : r1_tarski(k2_xboole_0('#skF_4',k3_xboole_0('#skF_4',C_345)),k2_xboole_0(k5_xboole_0('#skF_5','#skF_6'),C_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8111,c_8769])).

tff(c_8902,plain,(
    ! [C_348] : r1_tarski('#skF_4',k2_xboole_0(k5_xboole_0('#skF_5','#skF_6'),C_348)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8799])).

tff(c_8912,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8902])).

tff(c_8920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8258,c_8912])).

tff(c_8922,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_8110,plain,(
    k2_xboole_0('#skF_4',k5_xboole_0('#skF_5','#skF_6')) = k5_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_8102,c_8])).

tff(c_9005,plain,(
    ! [A_352] :
      ( r1_xboole_0(A_352,'#skF_4')
      | ~ r1_xboole_0(A_352,k5_xboole_0('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8110,c_28])).

tff(c_9010,plain,(
    r1_xboole_0(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_9005])).

tff(c_9017,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_9010,c_2])).

tff(c_8103,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_9107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8922,c_9017,c_8103,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:42:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.18/2.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.18/2.74  
% 8.18/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.18/2.75  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.18/2.75  
% 8.18/2.75  %Foreground sorts:
% 8.18/2.75  
% 8.18/2.75  
% 8.18/2.75  %Background operators:
% 8.18/2.75  
% 8.18/2.75  
% 8.18/2.75  %Foreground operators:
% 8.18/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.18/2.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.18/2.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.18/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.18/2.75  tff('#skF_5', type, '#skF_5': $i).
% 8.18/2.75  tff('#skF_6', type, '#skF_6': $i).
% 8.18/2.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.18/2.75  tff('#skF_2', type, '#skF_2': $i).
% 8.18/2.75  tff('#skF_3', type, '#skF_3': $i).
% 8.18/2.75  tff('#skF_1', type, '#skF_1': $i).
% 8.18/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.18/2.75  tff('#skF_4', type, '#skF_4': $i).
% 8.18/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.18/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.18/2.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.18/2.75  
% 8.18/2.76  tff(f_88, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 8.18/2.76  tff(f_81, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 8.18/2.76  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.18/2.76  tff(f_31, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 8.18/2.76  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.18/2.76  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.18/2.76  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.18/2.76  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.18/2.76  tff(f_45, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 8.18/2.76  tff(f_51, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.18/2.76  tff(f_79, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 8.18/2.76  tff(f_33, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 8.18/2.76  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 8.18/2.76  tff(c_38, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.18/2.76  tff(c_8258, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_38])).
% 8.18/2.76  tff(c_32, plain, (![A_32, B_33]: (k2_xboole_0(k5_xboole_0(A_32, B_33), k3_xboole_0(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.18/2.76  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.18/2.76  tff(c_40, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.18/2.76  tff(c_93, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_40])).
% 8.18/2.76  tff(c_4, plain, (![A_3, B_4]: (r1_xboole_0(k3_xboole_0(A_3, B_4), k5_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.18/2.76  tff(c_44, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.18/2.76  tff(c_141, plain, (r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_44])).
% 8.18/2.76  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.18/2.76  tff(c_148, plain, (k2_xboole_0('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_141, c_8])).
% 8.18/2.76  tff(c_28, plain, (![A_27, B_28, C_29]: (r1_xboole_0(A_27, B_28) | ~r1_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.18/2.76  tff(c_216, plain, (![A_65]: (r1_xboole_0(A_65, '#skF_4') | ~r1_xboole_0(A_65, k5_xboole_0('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_28])).
% 8.18/2.76  tff(c_226, plain, (r1_xboole_0(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_4, c_216])).
% 8.18/2.76  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.18/2.76  tff(c_240, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_226, c_2])).
% 8.18/2.76  tff(c_36, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.18/2.76  tff(c_265, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_36])).
% 8.18/2.76  tff(c_266, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_265])).
% 8.18/2.76  tff(c_12, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.18/2.76  tff(c_149, plain, (k3_xboole_0('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))='#skF_4'), inference(resolution, [status(thm)], [c_141, c_12])).
% 8.18/2.76  tff(c_475, plain, (![A_86, B_87, C_88]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_86, B_87), k3_xboole_0(A_86, C_88)), k2_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.18/2.76  tff(c_493, plain, (![C_88]: (r1_tarski(k2_xboole_0('#skF_4', k3_xboole_0('#skF_4', C_88)), k2_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), C_88)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_475])).
% 8.18/2.76  tff(c_503, plain, (![C_89]: (r1_tarski('#skF_4', k2_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), C_89)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_493])).
% 8.18/2.76  tff(c_513, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_503])).
% 8.18/2.76  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_513])).
% 8.18/2.76  tff(c_523, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_265])).
% 8.18/2.76  tff(c_540, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_240, c_38])).
% 8.18/2.76  tff(c_522, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_265])).
% 8.18/2.76  tff(c_18, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.18/2.76  tff(c_30, plain, (![A_30, B_31]: (k4_xboole_0(k2_xboole_0(A_30, B_31), B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.18/2.76  tff(c_45, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30])).
% 8.18/2.76  tff(c_529, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_522, c_45])).
% 8.18/2.76  tff(c_728, plain, (![A_93, B_94]: (k4_xboole_0(k2_xboole_0(A_93, B_94), k3_xboole_0(A_93, B_94))=k5_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.18/2.76  tff(c_16, plain, (![A_16, C_18, B_17]: (r1_tarski(k4_xboole_0(A_16, C_18), k4_xboole_0(B_17, C_18)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.18/2.76  tff(c_7295, plain, (![A_256, A_257, B_258]: (r1_tarski(k4_xboole_0(A_256, k3_xboole_0(A_257, B_258)), k5_xboole_0(A_257, B_258)) | ~r1_tarski(A_256, k2_xboole_0(A_257, B_258)))), inference(superposition, [status(thm), theory('equality')], [c_728, c_16])).
% 8.18/2.76  tff(c_7376, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_529, c_7295])).
% 8.18/2.76  tff(c_7410, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_7376])).
% 8.18/2.76  tff(c_7412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_7410])).
% 8.18/2.76  tff(c_7413, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 8.18/2.76  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.18/2.76  tff(c_7414, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_44])).
% 8.18/2.76  tff(c_42, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.18/2.76  tff(c_7445, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_7414, c_42])).
% 8.18/2.76  tff(c_7451, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_7445, c_45])).
% 8.18/2.76  tff(c_7628, plain, (![A_268, C_269, B_270]: (r1_tarski(k4_xboole_0(A_268, C_269), k4_xboole_0(B_270, C_269)) | ~r1_tarski(A_268, B_270))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.18/2.76  tff(c_8069, plain, (![B_304]: (r1_tarski('#skF_1', k4_xboole_0(B_304, k3_xboole_0('#skF_2', '#skF_3'))) | ~r1_tarski('#skF_1', B_304))), inference(superposition, [status(thm), theory('equality')], [c_7451, c_7628])).
% 8.18/2.76  tff(c_8083, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_8069])).
% 8.18/2.76  tff(c_8099, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7413, c_8083])).
% 8.18/2.76  tff(c_8101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_8099])).
% 8.36/2.76  tff(c_8102, plain, (r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_40])).
% 8.36/2.76  tff(c_8111, plain, (k3_xboole_0('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))='#skF_4'), inference(resolution, [status(thm)], [c_8102, c_12])).
% 8.36/2.76  tff(c_8769, plain, (![A_343, B_344, C_345]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_343, B_344), k3_xboole_0(A_343, C_345)), k2_xboole_0(B_344, C_345)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.36/2.76  tff(c_8799, plain, (![C_345]: (r1_tarski(k2_xboole_0('#skF_4', k3_xboole_0('#skF_4', C_345)), k2_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), C_345)))), inference(superposition, [status(thm), theory('equality')], [c_8111, c_8769])).
% 8.36/2.76  tff(c_8902, plain, (![C_348]: (r1_tarski('#skF_4', k2_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), C_348)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8799])).
% 8.36/2.76  tff(c_8912, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_8902])).
% 8.36/2.76  tff(c_8920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8258, c_8912])).
% 8.36/2.76  tff(c_8922, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_38])).
% 8.36/2.76  tff(c_8110, plain, (k2_xboole_0('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_8102, c_8])).
% 8.36/2.76  tff(c_9005, plain, (![A_352]: (r1_xboole_0(A_352, '#skF_4') | ~r1_xboole_0(A_352, k5_xboole_0('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8110, c_28])).
% 8.36/2.76  tff(c_9010, plain, (r1_xboole_0(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_4, c_9005])).
% 8.36/2.76  tff(c_9017, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_9010, c_2])).
% 8.36/2.76  tff(c_8103, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_40])).
% 8.36/2.76  tff(c_34, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.36/2.76  tff(c_9107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8922, c_9017, c_8103, c_34])).
% 8.36/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.36/2.76  
% 8.36/2.76  Inference rules
% 8.36/2.76  ----------------------
% 8.36/2.76  #Ref     : 0
% 8.36/2.76  #Sup     : 2515
% 8.36/2.76  #Fact    : 0
% 8.36/2.76  #Define  : 0
% 8.36/2.76  #Split   : 10
% 8.36/2.76  #Chain   : 0
% 8.36/2.76  #Close   : 0
% 8.36/2.76  
% 8.36/2.76  Ordering : KBO
% 8.36/2.76  
% 8.36/2.76  Simplification rules
% 8.36/2.76  ----------------------
% 8.36/2.76  #Subsume      : 201
% 8.36/2.76  #Demod        : 620
% 8.36/2.76  #Tautology    : 583
% 8.36/2.76  #SimpNegUnit  : 6
% 8.36/2.76  #BackRed      : 15
% 8.36/2.76  
% 8.36/2.76  #Partial instantiations: 0
% 8.36/2.76  #Strategies tried      : 1
% 8.36/2.76  
% 8.36/2.76  Timing (in seconds)
% 8.36/2.76  ----------------------
% 8.36/2.77  Preprocessing        : 0.30
% 8.36/2.77  Parsing              : 0.16
% 8.36/2.77  CNF conversion       : 0.02
% 8.36/2.77  Main loop            : 1.71
% 8.36/2.77  Inferencing          : 0.51
% 8.36/2.77  Reduction            : 0.67
% 8.36/2.77  Demodulation         : 0.51
% 8.36/2.77  BG Simplification    : 0.06
% 8.36/2.77  Subsumption          : 0.34
% 8.36/2.77  Abstraction          : 0.06
% 8.36/2.77  MUC search           : 0.00
% 8.36/2.77  Cooper               : 0.00
% 8.36/2.77  Total                : 2.04
% 8.36/2.77  Index Insertion      : 0.00
% 8.36/2.77  Index Deletion       : 0.00
% 8.36/2.77  Index Matching       : 0.00
% 8.36/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
