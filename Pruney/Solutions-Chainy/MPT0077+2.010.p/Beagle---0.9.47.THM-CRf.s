%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:36 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 350 expanded)
%              Number of leaves         :   24 ( 122 expanded)
%              Depth                    :    8
%              Number of atoms          :  185 ( 635 expanded)
%              Number of equality atoms :   60 ( 176 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_219,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | k3_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_251,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | k3_xboole_0(A_42,B_41) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_219,c_10])).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_187,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_266,plain,(
    k3_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_251,c_187])).

tff(c_84,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_99,plain,(
    ! [A_29,B_28] : r1_tarski(A_29,k2_xboole_0(B_28,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_37,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_268,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_274,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_4])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_12])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_288,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_294,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_288,c_4])).

tff(c_505,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k3_xboole_0(A_56,B_57),k3_xboole_0(A_56,C_58)) = k3_xboole_0(A_56,k2_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_542,plain,(
    ! [C_58] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_58)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_505])).

tff(c_575,plain,(
    ! [C_58] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_58)) = k3_xboole_0('#skF_4',C_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_542])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_39,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_34])).

tff(c_373,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_381,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_373])).

tff(c_1832,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_381])).

tff(c_1835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_1832])).

tff(c_1836,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_1847,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1836,c_10])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_xboole_0(A_13,C_15)
      | ~ r1_xboole_0(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3918,plain,(
    ! [A_179] :
      ( r1_xboole_0(A_179,'#skF_1')
      | ~ r1_tarski(A_179,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1847,c_16])).

tff(c_3935,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_99,c_3918])).

tff(c_3947,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3935,c_4])).

tff(c_3955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_3947])).

tff(c_3956,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_3976,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3956,c_10])).

tff(c_4015,plain,(
    ! [A_182,C_183,B_184] :
      ( r1_xboole_0(A_182,C_183)
      | ~ r1_xboole_0(B_184,C_183)
      | ~ r1_tarski(A_182,B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4740,plain,(
    ! [A_215] :
      ( r1_xboole_0(A_215,'#skF_1')
      | ~ r1_tarski(A_215,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3976,c_4015])).

tff(c_4757,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_99,c_4740])).

tff(c_4768,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4757,c_4])).

tff(c_4776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_4768])).

tff(c_4777,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_4793,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4777,c_10])).

tff(c_4824,plain,(
    ! [A_218,C_219,B_220] :
      ( r1_xboole_0(A_218,C_219)
      | ~ r1_xboole_0(B_220,C_219)
      | ~ r1_tarski(A_218,B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4921,plain,(
    ! [A_226] :
      ( r1_xboole_0(A_226,'#skF_1')
      | ~ r1_tarski(A_226,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_4793,c_4824])).

tff(c_4938,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_99,c_4921])).

tff(c_4947,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4938,c_4])).

tff(c_4954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_4947])).

tff(c_4956,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_4998,plain,(
    ! [A_232,B_233] :
      ( r1_xboole_0(A_232,B_233)
      | k3_xboole_0(A_232,B_233) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4955,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_4960,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4955])).

tff(c_5009,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4998,c_4960])).

tff(c_5070,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_5076,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5070,c_4])).

tff(c_5040,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_5046,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5040,c_4])).

tff(c_5348,plain,(
    ! [A_254,B_255,C_256] : k2_xboole_0(k3_xboole_0(A_254,B_255),k3_xboole_0(A_254,C_256)) = k3_xboole_0(A_254,k2_xboole_0(B_255,C_256)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6275,plain,(
    ! [A_293,C_294,B_295] : k2_xboole_0(k3_xboole_0(A_293,C_294),k3_xboole_0(A_293,B_295)) = k3_xboole_0(A_293,k2_xboole_0(B_295,C_294)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5348,c_2])).

tff(c_6387,plain,(
    ! [B_295] : k3_xboole_0('#skF_4',k2_xboole_0(B_295,'#skF_5')) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',B_295)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5046,c_6275])).

tff(c_6451,plain,(
    ! [B_295] : k3_xboole_0('#skF_4',k2_xboole_0(B_295,'#skF_5')) = k3_xboole_0('#skF_4',B_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_6387])).

tff(c_5090,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_5098,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_5090])).

tff(c_7573,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6451,c_5098])).

tff(c_7576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5076,c_7573])).

tff(c_7577,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_7595,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7577,c_4])).

tff(c_7890,plain,(
    ! [A_362,B_363,C_364] : k2_xboole_0(k3_xboole_0(A_362,B_363),k3_xboole_0(A_362,C_364)) = k3_xboole_0(A_362,k2_xboole_0(B_363,C_364)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8483,plain,(
    ! [A_389,B_390,C_391] : r1_tarski(k3_xboole_0(A_389,B_390),k3_xboole_0(A_389,k2_xboole_0(B_390,C_391))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7890,c_24])).

tff(c_8525,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7595,c_8483])).

tff(c_18,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7734,plain,(
    ! [A_353,B_354,C_355] :
      ( k1_xboole_0 = A_353
      | ~ r1_xboole_0(B_354,C_355)
      | ~ r1_tarski(A_353,C_355)
      | ~ r1_tarski(A_353,B_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7782,plain,(
    ! [A_353] :
      ( k1_xboole_0 = A_353
      | ~ r1_tarski(A_353,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_7734])).

tff(c_8599,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8525,c_7782])).

tff(c_8605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5009,c_8599])).

tff(c_8606,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_8622,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8606,c_4])).

tff(c_8858,plain,(
    ! [A_407,B_408,C_409] : k2_xboole_0(k3_xboole_0(A_407,B_408),k3_xboole_0(A_407,C_409)) = k3_xboole_0(A_407,k2_xboole_0(B_408,C_409)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9162,plain,(
    ! [A_421,B_422,C_423] : r1_tarski(k3_xboole_0(A_421,B_422),k3_xboole_0(A_421,k2_xboole_0(B_422,C_423))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8858,c_24])).

tff(c_9180,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8622,c_9162])).

tff(c_8735,plain,(
    ! [A_399,B_400,C_401] :
      ( k1_xboole_0 = A_399
      | ~ r1_xboole_0(B_400,C_401)
      | ~ r1_tarski(A_399,C_401)
      | ~ r1_tarski(A_399,B_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8771,plain,(
    ! [A_399] :
      ( k1_xboole_0 = A_399
      | ~ r1_tarski(A_399,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_8735])).

tff(c_9230,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9180,c_8771])).

tff(c_9236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5009,c_9230])).

tff(c_9237,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_9272,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9237,c_4])).

tff(c_9584,plain,(
    ! [A_443,B_444,C_445] : k2_xboole_0(k3_xboole_0(A_443,B_444),k3_xboole_0(A_443,C_445)) = k3_xboole_0(A_443,k2_xboole_0(B_444,C_445)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9907,plain,(
    ! [A_458,B_459,C_460] : r1_tarski(k3_xboole_0(A_458,B_459),k3_xboole_0(A_458,k2_xboole_0(B_459,C_460))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9584,c_24])).

tff(c_9937,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9272,c_9907])).

tff(c_9445,plain,(
    ! [A_435,B_436,C_437] :
      ( k1_xboole_0 = A_435
      | ~ r1_xboole_0(B_436,C_437)
      | ~ r1_tarski(A_435,C_437)
      | ~ r1_tarski(A_435,B_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9490,plain,(
    ! [A_435] :
      ( k1_xboole_0 = A_435
      | ~ r1_tarski(A_435,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_9445])).

tff(c_9991,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9937,c_9490])).

tff(c_9997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5009,c_9991])).

tff(c_9999,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_4955])).

tff(c_36,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_12666,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_9999,c_38])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10001,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_9999,c_32])).

tff(c_10069,plain,(
    ! [A_468,B_469] :
      ( k3_xboole_0(A_468,B_469) = k1_xboole_0
      | ~ r1_xboole_0(A_468,B_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10105,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10001,c_10069])).

tff(c_9998,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_4955])).

tff(c_10107,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9998,c_10069])).

tff(c_10370,plain,(
    ! [A_484,B_485,C_486] : k2_xboole_0(k3_xboole_0(A_484,B_485),k3_xboole_0(A_484,C_486)) = k3_xboole_0(A_484,k2_xboole_0(B_485,C_486)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11460,plain,(
    ! [A_524,C_525,B_526] : k2_xboole_0(k3_xboole_0(A_524,C_525),k3_xboole_0(A_524,B_526)) = k3_xboole_0(A_524,k2_xboole_0(B_526,C_525)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10370,c_2])).

tff(c_11587,plain,(
    ! [C_525] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_525)) = k2_xboole_0(k3_xboole_0('#skF_4',C_525),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10107,c_11460])).

tff(c_11659,plain,(
    ! [C_525] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_525)) = k3_xboole_0('#skF_4',C_525) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2,c_11587])).

tff(c_10140,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_10156,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_10140])).

tff(c_12647,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11659,c_10156])).

tff(c_12650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10105,c_12647])).

tff(c_12652,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_12678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12666,c_12652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.53/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.70  
% 7.65/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.70  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.65/2.70  
% 7.65/2.70  %Foreground sorts:
% 7.65/2.70  
% 7.65/2.70  
% 7.65/2.70  %Background operators:
% 7.65/2.70  
% 7.65/2.70  
% 7.65/2.70  %Foreground operators:
% 7.65/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.65/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.70  tff('#skF_5', type, '#skF_5': $i).
% 7.65/2.70  tff('#skF_6', type, '#skF_6': $i).
% 7.65/2.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.65/2.70  tff('#skF_2', type, '#skF_2': $i).
% 7.65/2.70  tff('#skF_3', type, '#skF_3': $i).
% 7.65/2.70  tff('#skF_1', type, '#skF_1': $i).
% 7.65/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.70  tff('#skF_4', type, '#skF_4': $i).
% 7.65/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.65/2.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.65/2.70  
% 7.65/2.72  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.65/2.72  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.65/2.72  tff(f_86, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.65/2.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.65/2.72  tff(f_69, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.65/2.72  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.65/2.72  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 7.65/2.72  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.65/2.72  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 7.65/2.72  tff(f_67, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 7.65/2.72  tff(c_219, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | k3_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.72  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.65/2.72  tff(c_251, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | k3_xboole_0(A_42, B_41)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_219, c_10])).
% 7.65/2.72  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.65/2.72  tff(c_187, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 7.65/2.72  tff(c_266, plain, (k3_xboole_0('#skF_2', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_251, c_187])).
% 7.65/2.72  tff(c_84, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.65/2.72  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.65/2.72  tff(c_99, plain, (![A_29, B_28]: (r1_tarski(A_29, k2_xboole_0(B_28, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_24])).
% 7.65/2.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.65/2.73  tff(c_30, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.65/2.73  tff(c_37, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 7.65/2.73  tff(c_268, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_37])).
% 7.65/2.73  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.73  tff(c_274, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_4])).
% 7.65/2.73  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.65/2.73  tff(c_106, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_84, c_12])).
% 7.65/2.73  tff(c_26, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.65/2.73  tff(c_40, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 7.65/2.73  tff(c_288, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_40])).
% 7.65/2.73  tff(c_294, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_288, c_4])).
% 7.65/2.73  tff(c_505, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k3_xboole_0(A_56, B_57), k3_xboole_0(A_56, C_58))=k3_xboole_0(A_56, k2_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.73  tff(c_542, plain, (![C_58]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_58))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_58)))), inference(superposition, [status(thm), theory('equality')], [c_294, c_505])).
% 7.65/2.73  tff(c_575, plain, (![C_58]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_58))=k3_xboole_0('#skF_4', C_58))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_542])).
% 7.65/2.73  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.73  tff(c_34, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.65/2.73  tff(c_39, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_34])).
% 7.65/2.73  tff(c_373, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_39])).
% 7.65/2.73  tff(c_381, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_373])).
% 7.65/2.73  tff(c_1832, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_575, c_381])).
% 7.65/2.73  tff(c_1835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_1832])).
% 7.65/2.73  tff(c_1836, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_39])).
% 7.65/2.73  tff(c_1847, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1836, c_10])).
% 7.65/2.73  tff(c_16, plain, (![A_13, C_15, B_14]: (r1_xboole_0(A_13, C_15) | ~r1_xboole_0(B_14, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.65/2.73  tff(c_3918, plain, (![A_179]: (r1_xboole_0(A_179, '#skF_1') | ~r1_tarski(A_179, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_1847, c_16])).
% 7.65/2.73  tff(c_3935, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_99, c_3918])).
% 7.65/2.73  tff(c_3947, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_3935, c_4])).
% 7.65/2.73  tff(c_3955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_3947])).
% 7.65/2.73  tff(c_3956, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 7.65/2.73  tff(c_3976, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_3956, c_10])).
% 7.65/2.73  tff(c_4015, plain, (![A_182, C_183, B_184]: (r1_xboole_0(A_182, C_183) | ~r1_xboole_0(B_184, C_183) | ~r1_tarski(A_182, B_184))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.65/2.73  tff(c_4740, plain, (![A_215]: (r1_xboole_0(A_215, '#skF_1') | ~r1_tarski(A_215, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_3976, c_4015])).
% 7.65/2.73  tff(c_4757, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_99, c_4740])).
% 7.65/2.73  tff(c_4768, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_4757, c_4])).
% 7.65/2.73  tff(c_4776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_4768])).
% 7.65/2.73  tff(c_4777, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_37])).
% 7.65/2.73  tff(c_4793, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_4777, c_10])).
% 7.65/2.73  tff(c_4824, plain, (![A_218, C_219, B_220]: (r1_xboole_0(A_218, C_219) | ~r1_xboole_0(B_220, C_219) | ~r1_tarski(A_218, B_220))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.65/2.73  tff(c_4921, plain, (![A_226]: (r1_xboole_0(A_226, '#skF_1') | ~r1_tarski(A_226, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_4793, c_4824])).
% 7.65/2.73  tff(c_4938, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_99, c_4921])).
% 7.65/2.73  tff(c_4947, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_4938, c_4])).
% 7.65/2.73  tff(c_4954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_4947])).
% 7.65/2.73  tff(c_4956, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 7.65/2.73  tff(c_4998, plain, (![A_232, B_233]: (r1_xboole_0(A_232, B_233) | k3_xboole_0(A_232, B_233)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.73  tff(c_4955, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_28])).
% 7.65/2.73  tff(c_4960, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_4955])).
% 7.65/2.73  tff(c_5009, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4998, c_4960])).
% 7.65/2.73  tff(c_5070, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_40])).
% 7.65/2.73  tff(c_5076, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_5070, c_4])).
% 7.65/2.73  tff(c_5040, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_37])).
% 7.65/2.73  tff(c_5046, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_5040, c_4])).
% 7.65/2.73  tff(c_5348, plain, (![A_254, B_255, C_256]: (k2_xboole_0(k3_xboole_0(A_254, B_255), k3_xboole_0(A_254, C_256))=k3_xboole_0(A_254, k2_xboole_0(B_255, C_256)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.73  tff(c_6275, plain, (![A_293, C_294, B_295]: (k2_xboole_0(k3_xboole_0(A_293, C_294), k3_xboole_0(A_293, B_295))=k3_xboole_0(A_293, k2_xboole_0(B_295, C_294)))), inference(superposition, [status(thm), theory('equality')], [c_5348, c_2])).
% 7.65/2.73  tff(c_6387, plain, (![B_295]: (k3_xboole_0('#skF_4', k2_xboole_0(B_295, '#skF_5'))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', B_295)))), inference(superposition, [status(thm), theory('equality')], [c_5046, c_6275])).
% 7.65/2.73  tff(c_6451, plain, (![B_295]: (k3_xboole_0('#skF_4', k2_xboole_0(B_295, '#skF_5'))=k3_xboole_0('#skF_4', B_295))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_6387])).
% 7.65/2.73  tff(c_5090, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_39])).
% 7.65/2.73  tff(c_5098, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_5090])).
% 7.65/2.73  tff(c_7573, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6451, c_5098])).
% 7.65/2.73  tff(c_7576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5076, c_7573])).
% 7.65/2.73  tff(c_7577, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_39])).
% 7.65/2.73  tff(c_7595, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_7577, c_4])).
% 7.65/2.73  tff(c_7890, plain, (![A_362, B_363, C_364]: (k2_xboole_0(k3_xboole_0(A_362, B_363), k3_xboole_0(A_362, C_364))=k3_xboole_0(A_362, k2_xboole_0(B_363, C_364)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.73  tff(c_8483, plain, (![A_389, B_390, C_391]: (r1_tarski(k3_xboole_0(A_389, B_390), k3_xboole_0(A_389, k2_xboole_0(B_390, C_391))))), inference(superposition, [status(thm), theory('equality')], [c_7890, c_24])).
% 7.65/2.73  tff(c_8525, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7595, c_8483])).
% 7.65/2.73  tff(c_18, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.65/2.73  tff(c_7734, plain, (![A_353, B_354, C_355]: (k1_xboole_0=A_353 | ~r1_xboole_0(B_354, C_355) | ~r1_tarski(A_353, C_355) | ~r1_tarski(A_353, B_354))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.65/2.73  tff(c_7782, plain, (![A_353]: (k1_xboole_0=A_353 | ~r1_tarski(A_353, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_7734])).
% 7.65/2.73  tff(c_8599, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_8525, c_7782])).
% 7.65/2.73  tff(c_8605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5009, c_8599])).
% 7.65/2.73  tff(c_8606, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 7.65/2.73  tff(c_8622, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_8606, c_4])).
% 7.65/2.73  tff(c_8858, plain, (![A_407, B_408, C_409]: (k2_xboole_0(k3_xboole_0(A_407, B_408), k3_xboole_0(A_407, C_409))=k3_xboole_0(A_407, k2_xboole_0(B_408, C_409)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.73  tff(c_9162, plain, (![A_421, B_422, C_423]: (r1_tarski(k3_xboole_0(A_421, B_422), k3_xboole_0(A_421, k2_xboole_0(B_422, C_423))))), inference(superposition, [status(thm), theory('equality')], [c_8858, c_24])).
% 7.65/2.73  tff(c_9180, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8622, c_9162])).
% 7.65/2.73  tff(c_8735, plain, (![A_399, B_400, C_401]: (k1_xboole_0=A_399 | ~r1_xboole_0(B_400, C_401) | ~r1_tarski(A_399, C_401) | ~r1_tarski(A_399, B_400))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.65/2.73  tff(c_8771, plain, (![A_399]: (k1_xboole_0=A_399 | ~r1_tarski(A_399, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_8735])).
% 7.65/2.73  tff(c_9230, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_9180, c_8771])).
% 7.65/2.73  tff(c_9236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5009, c_9230])).
% 7.65/2.73  tff(c_9237, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_37])).
% 7.65/2.73  tff(c_9272, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_9237, c_4])).
% 7.65/2.73  tff(c_9584, plain, (![A_443, B_444, C_445]: (k2_xboole_0(k3_xboole_0(A_443, B_444), k3_xboole_0(A_443, C_445))=k3_xboole_0(A_443, k2_xboole_0(B_444, C_445)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.73  tff(c_9907, plain, (![A_458, B_459, C_460]: (r1_tarski(k3_xboole_0(A_458, B_459), k3_xboole_0(A_458, k2_xboole_0(B_459, C_460))))), inference(superposition, [status(thm), theory('equality')], [c_9584, c_24])).
% 7.65/2.73  tff(c_9937, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9272, c_9907])).
% 7.65/2.73  tff(c_9445, plain, (![A_435, B_436, C_437]: (k1_xboole_0=A_435 | ~r1_xboole_0(B_436, C_437) | ~r1_tarski(A_435, C_437) | ~r1_tarski(A_435, B_436))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.65/2.73  tff(c_9490, plain, (![A_435]: (k1_xboole_0=A_435 | ~r1_tarski(A_435, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_9445])).
% 7.65/2.73  tff(c_9991, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_9937, c_9490])).
% 7.65/2.73  tff(c_9997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5009, c_9991])).
% 7.65/2.73  tff(c_9999, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_4955])).
% 7.65/2.73  tff(c_36, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.65/2.73  tff(c_38, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 7.65/2.73  tff(c_12666, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_9999, c_38])).
% 7.65/2.73  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.65/2.73  tff(c_10001, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_9999, c_32])).
% 7.65/2.73  tff(c_10069, plain, (![A_468, B_469]: (k3_xboole_0(A_468, B_469)=k1_xboole_0 | ~r1_xboole_0(A_468, B_469))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.73  tff(c_10105, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_10001, c_10069])).
% 7.65/2.73  tff(c_9998, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_4955])).
% 7.65/2.73  tff(c_10107, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_9998, c_10069])).
% 7.65/2.73  tff(c_10370, plain, (![A_484, B_485, C_486]: (k2_xboole_0(k3_xboole_0(A_484, B_485), k3_xboole_0(A_484, C_486))=k3_xboole_0(A_484, k2_xboole_0(B_485, C_486)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.73  tff(c_11460, plain, (![A_524, C_525, B_526]: (k2_xboole_0(k3_xboole_0(A_524, C_525), k3_xboole_0(A_524, B_526))=k3_xboole_0(A_524, k2_xboole_0(B_526, C_525)))), inference(superposition, [status(thm), theory('equality')], [c_10370, c_2])).
% 7.65/2.73  tff(c_11587, plain, (![C_525]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_525))=k2_xboole_0(k3_xboole_0('#skF_4', C_525), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10107, c_11460])).
% 7.65/2.73  tff(c_11659, plain, (![C_525]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_525))=k3_xboole_0('#skF_4', C_525))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2, c_11587])).
% 7.65/2.73  tff(c_10140, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_39])).
% 7.65/2.73  tff(c_10156, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_10140])).
% 7.65/2.73  tff(c_12647, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11659, c_10156])).
% 7.65/2.73  tff(c_12650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10105, c_12647])).
% 7.65/2.73  tff(c_12652, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_39])).
% 7.65/2.73  tff(c_12678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12666, c_12652])).
% 7.65/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.73  
% 7.65/2.73  Inference rules
% 7.65/2.73  ----------------------
% 7.65/2.73  #Ref     : 0
% 7.65/2.73  #Sup     : 3130
% 7.65/2.73  #Fact    : 0
% 7.65/2.73  #Define  : 0
% 7.65/2.73  #Split   : 53
% 7.65/2.73  #Chain   : 0
% 7.65/2.73  #Close   : 0
% 7.65/2.73  
% 7.65/2.73  Ordering : KBO
% 7.65/2.73  
% 7.65/2.73  Simplification rules
% 7.65/2.73  ----------------------
% 7.65/2.73  #Subsume      : 302
% 7.65/2.73  #Demod        : 1780
% 7.65/2.73  #Tautology    : 1317
% 7.65/2.73  #SimpNegUnit  : 7
% 7.65/2.73  #BackRed      : 20
% 7.65/2.73  
% 7.65/2.73  #Partial instantiations: 0
% 7.65/2.73  #Strategies tried      : 1
% 7.65/2.73  
% 7.65/2.73  Timing (in seconds)
% 7.65/2.73  ----------------------
% 7.65/2.73  Preprocessing        : 0.29
% 7.65/2.73  Parsing              : 0.17
% 7.65/2.73  CNF conversion       : 0.02
% 7.65/2.73  Main loop            : 1.66
% 7.65/2.73  Inferencing          : 0.53
% 7.65/2.73  Reduction            : 0.60
% 7.65/2.73  Demodulation         : 0.43
% 7.65/2.73  BG Simplification    : 0.05
% 7.65/2.73  Subsumption          : 0.35
% 7.65/2.73  Abstraction          : 0.07
% 7.65/2.73  MUC search           : 0.00
% 7.65/2.73  Cooper               : 0.00
% 7.65/2.73  Total                : 2.00
% 7.65/2.73  Index Insertion      : 0.00
% 7.65/2.73  Index Deletion       : 0.00
% 7.65/2.73  Index Matching       : 0.00
% 7.65/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
