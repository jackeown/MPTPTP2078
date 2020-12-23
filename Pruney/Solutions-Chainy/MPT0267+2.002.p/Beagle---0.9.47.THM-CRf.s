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
% DateTime   : Thu Dec  3 09:52:32 EST 2020

% Result     : Theorem 9.46s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 426 expanded)
%              Number of leaves         :   35 ( 148 expanded)
%              Depth                    :   13
%              Number of atoms          :  261 ( 905 expanded)
%              Number of equality atoms :   28 ( 152 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_32,plain,(
    ! [C_24] : r2_hidden(C_24,k1_tarski(C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,
    ( '#skF_7' != '#skF_5'
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_130,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_210,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_28,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_305,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,B_94)
      | ~ r2_hidden(C_95,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_324,plain,(
    ! [C_96,B_97,A_98] :
      ( ~ r2_hidden(C_96,B_97)
      | ~ r2_hidden(C_96,k4_xboole_0(A_98,B_97)) ) ),
    inference(resolution,[status(thm)],[c_28,c_305])).

tff(c_336,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_210,c_324])).

tff(c_56,plain,(
    ! [B_49,A_48] :
      ( k3_xboole_0(B_49,k1_tarski(A_48)) = k1_tarski(A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_129,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_26,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1604,plain,(
    ! [A_2218,B_2219,C_2220] :
      ( r2_hidden(A_2218,B_2219)
      | r2_hidden(A_2218,C_2220)
      | ~ r2_hidden(A_2218,k5_xboole_0(B_2219,C_2220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4578,plain,(
    ! [A_4796,A_4797,B_4798] :
      ( r2_hidden(A_4796,A_4797)
      | r2_hidden(A_4796,k3_xboole_0(A_4797,B_4798))
      | ~ r2_hidden(A_4796,k4_xboole_0(A_4797,B_4798)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1604])).

tff(c_4595,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_210,c_4578])).

tff(c_4610,plain,(
    r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_4595])).

tff(c_4680,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_10'))
    | ~ r2_hidden('#skF_10','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4610])).

tff(c_4689,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_4680])).

tff(c_54,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),B_47)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_134,plain,(
    ! [A_1,B_2,C_64] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_64,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_4686,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_4610,c_134])).

tff(c_4706,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_4686])).

tff(c_4712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4689,c_4706])).

tff(c_4713,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_5997,plain,(
    ! [A_7012,C_7013,B_7014] :
      ( r2_hidden(A_7012,C_7013)
      | ~ r2_hidden(A_7012,B_7014)
      | r2_hidden(A_7012,k5_xboole_0(B_7014,C_7013)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9624,plain,(
    ! [A_9816,A_9817,B_9818] :
      ( r2_hidden(A_9816,k3_xboole_0(A_9817,B_9818))
      | ~ r2_hidden(A_9816,A_9817)
      | r2_hidden(A_9816,k4_xboole_0(A_9817,B_9818)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5997])).

tff(c_4714,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4762,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4714,c_64])).

tff(c_9672,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_9624,c_4762])).

tff(c_9697,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4713,c_9672])).

tff(c_5981,plain,(
    ! [A_6967,B_6968,C_6969] :
      ( r2_hidden(A_6967,B_6968)
      | ~ r2_hidden(A_6967,C_6969)
      | r2_hidden(A_6967,k5_xboole_0(B_6968,C_6969)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5994,plain,(
    ! [A_6967,A_16,B_17] :
      ( r2_hidden(A_6967,A_16)
      | ~ r2_hidden(A_6967,k3_xboole_0(A_16,B_17))
      | r2_hidden(A_6967,k4_xboole_0(A_16,B_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5981])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4810,plain,(
    ! [A_4984,B_4985,C_4986] :
      ( ~ r1_xboole_0(A_4984,B_4985)
      | ~ r2_hidden(C_4986,B_4985)
      | ~ r2_hidden(C_4986,A_4984) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5880,plain,(
    ! [C_6702,B_6703,A_6704] :
      ( ~ r2_hidden(C_6702,B_6703)
      | ~ r2_hidden(C_6702,k1_tarski(A_6704))
      | r2_hidden(A_6704,B_6703) ) ),
    inference(resolution,[status(thm)],[c_54,c_4810])).

tff(c_5928,plain,(
    ! [C_6835,A_6836] :
      ( ~ r2_hidden(C_6835,k1_tarski(A_6836))
      | r2_hidden(A_6836,k1_tarski(C_6835)) ) ),
    inference(resolution,[status(thm)],[c_32,c_5880])).

tff(c_6759,plain,(
    ! [A_8022,A_8023] :
      ( r2_hidden(A_8022,k1_tarski('#skF_1'(A_8023,k1_tarski(A_8022))))
      | r1_xboole_0(A_8023,k1_tarski(A_8022)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5928])).

tff(c_5895,plain,(
    ! [A_6704] :
      ( ~ r2_hidden('#skF_5',k1_tarski(A_6704))
      | r2_hidden(A_6704,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4713,c_5880])).

tff(c_6916,plain,(
    ! [A_8023] :
      ( r2_hidden('#skF_1'(A_8023,k1_tarski('#skF_5')),'#skF_6')
      | r1_xboole_0(A_8023,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6759,c_5895])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4890,plain,(
    ! [C_4999,B_5000,A_5001] :
      ( ~ r2_hidden(C_4999,B_5000)
      | ~ r2_hidden(C_4999,k4_xboole_0(A_5001,B_5000)) ) ),
    inference(resolution,[status(thm)],[c_28,c_4810])).

tff(c_9210,plain,(
    ! [A_9166,B_9167,B_9168] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_9166,B_9167),B_9168),B_9167)
      | r1_xboole_0(k4_xboole_0(A_9166,B_9167),B_9168) ) ),
    inference(resolution,[status(thm)],[c_20,c_4890])).

tff(c_9347,plain,(
    ! [A_9298] : r1_xboole_0(k4_xboole_0(A_9298,'#skF_6'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6916,c_9210])).

tff(c_4763,plain,(
    ! [B_4982,A_4983] :
      ( k3_xboole_0(B_4982,k1_tarski(A_4983)) = k1_tarski(A_4983)
      | ~ r2_hidden(A_4983,B_4982) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_153,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,k3_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_162,plain,(
    ! [A_11,B_12,A_67] :
      ( ~ r1_xboole_0(A_11,B_12)
      | r1_xboole_0(A_67,k3_xboole_0(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_153,c_24])).

tff(c_4784,plain,(
    ! [B_4982,A_4983,A_67] :
      ( ~ r1_xboole_0(B_4982,k1_tarski(A_4983))
      | r1_xboole_0(A_67,k1_tarski(A_4983))
      | ~ r2_hidden(A_4983,B_4982) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4763,c_162])).

tff(c_9409,plain,(
    ! [A_67,A_9298] :
      ( r1_xboole_0(A_67,k1_tarski('#skF_5'))
      | ~ r2_hidden('#skF_5',k4_xboole_0(A_9298,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_9347,c_4784])).

tff(c_9589,plain,(
    ! [A_9687] : ~ r2_hidden('#skF_5',k4_xboole_0(A_9687,'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_9409])).

tff(c_9596,plain,(
    ! [A_9730] :
      ( r2_hidden('#skF_5',A_9730)
      | ~ r2_hidden('#skF_5',k3_xboole_0(A_9730,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_5994,c_9589])).

tff(c_9605,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_5',A_1)
      | ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6',A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9596])).

tff(c_9769,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_9697,c_9605])).

tff(c_30,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9836,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9769,c_30])).

tff(c_9899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_9836])).

tff(c_9904,plain,(
    ! [A_10071] : r1_xboole_0(A_10071,k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9409])).

tff(c_4790,plain,(
    ! [B_4982,A_4983,C_15] :
      ( ~ r1_xboole_0(B_4982,k1_tarski(A_4983))
      | ~ r2_hidden(C_15,k1_tarski(A_4983))
      | ~ r2_hidden(A_4983,B_4982) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4763,c_24])).

tff(c_9980,plain,(
    ! [C_15,A_10071] :
      ( ~ r2_hidden(C_15,k1_tarski('#skF_5'))
      | ~ r2_hidden('#skF_5',A_10071) ) ),
    inference(resolution,[status(thm)],[c_9904,c_4790])).

tff(c_10092,plain,(
    ! [A_10071] : ~ r2_hidden('#skF_5',A_10071) ),
    inference(splitLeft,[status(thm)],[c_9980])).

tff(c_10094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10092,c_4713])).

tff(c_10096,plain,(
    ! [C_10202] : ~ r2_hidden(C_10202,k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9980])).

tff(c_10122,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_32,c_10096])).

tff(c_10123,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_10242,plain,(
    ! [A_10268,B_10269,C_10270] :
      ( ~ r1_xboole_0(A_10268,B_10269)
      | ~ r2_hidden(C_10270,B_10269)
      | ~ r2_hidden(C_10270,A_10268) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10258,plain,(
    ! [C_10271,B_10272,A_10273] :
      ( ~ r2_hidden(C_10271,B_10272)
      | ~ r2_hidden(C_10271,k4_xboole_0(A_10273,B_10272)) ) ),
    inference(resolution,[status(thm)],[c_28,c_10242])).

tff(c_10272,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_10123,c_10258])).

tff(c_10479,plain,(
    ! [A_10299,B_10300,C_10301] :
      ( r2_hidden(A_10299,B_10300)
      | r2_hidden(A_10299,C_10301)
      | ~ r2_hidden(A_10299,k5_xboole_0(B_10300,C_10301)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14183,plain,(
    ! [A_14624,A_14625,B_14626] :
      ( r2_hidden(A_14624,A_14625)
      | r2_hidden(A_14624,k3_xboole_0(A_14625,B_14626))
      | ~ r2_hidden(A_14624,k4_xboole_0(A_14625,B_14626)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_10479])).

tff(c_14208,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_10123,c_14183])).

tff(c_14216,plain,(
    r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_14208])).

tff(c_14287,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_10'))
    | ~ r2_hidden('#skF_10','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_14216])).

tff(c_14298,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_10272,c_14287])).

tff(c_10158,plain,(
    ! [A_10251,B_10252,C_10253] :
      ( ~ r1_xboole_0(A_10251,B_10252)
      | ~ r2_hidden(C_10253,k3_xboole_0(A_10251,B_10252)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10172,plain,(
    ! [B_2,A_1,C_10253] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_10253,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10158])).

tff(c_14294,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_14216,c_10172])).

tff(c_14315,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_14294])).

tff(c_14321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14298,c_14315])).

tff(c_14322,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_14330,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_14322])).

tff(c_14323,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14324,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_14326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14323,c_14324])).

tff(c_14327,plain,
    ( '#skF_10' = '#skF_8'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_14331,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_14327])).

tff(c_14681,plain,(
    ! [A_14851,C_14852,B_14853] :
      ( r2_hidden(A_14851,C_14852)
      | ~ r2_hidden(A_14851,B_14853)
      | r2_hidden(A_14851,k5_xboole_0(B_14853,C_14852)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_17891,plain,(
    ! [A_19225,A_19226,B_19227] :
      ( r2_hidden(A_19225,k3_xboole_0(A_19226,B_19227))
      | ~ r2_hidden(A_19225,A_19226)
      | r2_hidden(A_19225,k4_xboole_0(A_19226,B_19227)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_14681])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14526,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14323,c_58])).

tff(c_14527,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_14526])).

tff(c_17944,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_17891,c_14527])).

tff(c_17964,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14331,c_17944])).

tff(c_14780,plain,(
    ! [A_14868,B_14869,C_14870] :
      ( r2_hidden(A_14868,B_14869)
      | ~ r2_hidden(A_14868,C_14870)
      | r2_hidden(A_14868,k5_xboole_0(B_14869,C_14870)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_17501,plain,(
    ! [A_18568,A_18569,B_18570] :
      ( r2_hidden(A_18568,A_18569)
      | ~ r2_hidden(A_18568,k3_xboole_0(A_18569,B_18570))
      | r2_hidden(A_18568,k4_xboole_0(A_18569,B_18570)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_14780])).

tff(c_14602,plain,(
    ! [A_14838,B_14839] :
      ( r2_hidden('#skF_2'(A_14838,B_14839),k3_xboole_0(A_14838,B_14839))
      | r1_xboole_0(A_14838,B_14839) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14338,plain,(
    ! [A_14797,B_14798,C_14799] :
      ( ~ r1_xboole_0(A_14797,B_14798)
      | ~ r2_hidden(C_14799,k3_xboole_0(A_14797,B_14798)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14345,plain,(
    ! [A_1,B_2,C_14799] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_14799,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14338])).

tff(c_14623,plain,(
    ! [B_14840,A_14841] :
      ( ~ r1_xboole_0(B_14840,A_14841)
      | r1_xboole_0(A_14841,B_14840) ) ),
    inference(resolution,[status(thm)],[c_14602,c_14345])).

tff(c_14648,plain,(
    ! [B_14842,A_14843] : r1_xboole_0(B_14842,k4_xboole_0(A_14843,B_14842)) ),
    inference(resolution,[status(thm)],[c_28,c_14623])).

tff(c_16,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14655,plain,(
    ! [C_10,A_14843,B_14842] :
      ( ~ r2_hidden(C_10,k4_xboole_0(A_14843,B_14842))
      | ~ r2_hidden(C_10,B_14842) ) ),
    inference(resolution,[status(thm)],[c_14648,c_16])).

tff(c_17817,plain,(
    ! [A_19135,B_19136,A_19137] :
      ( ~ r2_hidden(A_19135,B_19136)
      | r2_hidden(A_19135,A_19137)
      | ~ r2_hidden(A_19135,k3_xboole_0(A_19137,B_19136)) ) ),
    inference(resolution,[status(thm)],[c_17501,c_14655])).

tff(c_17845,plain,(
    ! [A_19135,B_2,A_1] :
      ( ~ r2_hidden(A_19135,B_2)
      | r2_hidden(A_19135,A_1)
      | ~ r2_hidden(A_19135,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17817])).

tff(c_17967,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_17964,c_17845])).

tff(c_18040,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14331,c_17967])).

tff(c_18151,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_18040,c_30])).

tff(c_18211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14330,c_18151])).

tff(c_18212,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_14526])).

tff(c_18213,plain,(
    r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_14526])).

tff(c_18279,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18212,c_18213,c_64])).

tff(c_14506,plain,(
    ! [A_14826,B_14827,C_14828] :
      ( ~ r1_xboole_0(A_14826,B_14827)
      | ~ r2_hidden(C_14828,B_14827)
      | ~ r2_hidden(C_14828,A_14826) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14524,plain,(
    ! [C_14828,B_19,A_18] :
      ( ~ r2_hidden(C_14828,B_19)
      | ~ r2_hidden(C_14828,k4_xboole_0(A_18,B_19)) ) ),
    inference(resolution,[status(thm)],[c_28,c_14506])).

tff(c_18282,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_18279,c_14524])).

tff(c_18286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18282])).

tff(c_18288,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_14327])).

tff(c_18287,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_14327])).

tff(c_18366,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18287,c_68])).

tff(c_18367,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_18288,c_18366])).

tff(c_18471,plain,(
    ! [A_19563,B_19564,C_19565] :
      ( ~ r1_xboole_0(A_19563,B_19564)
      | ~ r2_hidden(C_19565,B_19564)
      | ~ r2_hidden(C_19565,A_19563) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18490,plain,(
    ! [C_19566,B_19567,A_19568] :
      ( ~ r2_hidden(C_19566,B_19567)
      | ~ r2_hidden(C_19566,k4_xboole_0(A_19568,B_19567)) ) ),
    inference(resolution,[status(thm)],[c_28,c_18471])).

tff(c_18493,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_18367,c_18490])).

tff(c_18505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18493])).

tff(c_18506,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_14322])).

tff(c_18507,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_14322])).

tff(c_18533,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18506,c_18507,c_66])).

tff(c_18639,plain,(
    ! [A_19595,B_19596,C_19597] :
      ( ~ r1_xboole_0(A_19595,B_19596)
      | ~ r2_hidden(C_19597,B_19596)
      | ~ r2_hidden(C_19597,A_19595) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18658,plain,(
    ! [C_19598,B_19599,A_19600] :
      ( ~ r2_hidden(C_19598,B_19599)
      | ~ r2_hidden(C_19598,k4_xboole_0(A_19600,B_19599)) ) ),
    inference(resolution,[status(thm)],[c_28,c_18639])).

tff(c_18669,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_18533,c_18658])).

tff(c_18675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.46/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.46/3.18  
% 9.46/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.46/3.18  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 9.46/3.18  
% 9.46/3.18  %Foreground sorts:
% 9.46/3.18  
% 9.46/3.18  
% 9.46/3.18  %Background operators:
% 9.46/3.18  
% 9.46/3.18  
% 9.46/3.18  %Foreground operators:
% 9.46/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.46/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.46/3.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.46/3.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.46/3.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.46/3.18  tff('#skF_7', type, '#skF_7': $i).
% 9.46/3.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.46/3.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.46/3.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.46/3.18  tff('#skF_10', type, '#skF_10': $i).
% 9.46/3.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.46/3.18  tff('#skF_5', type, '#skF_5': $i).
% 9.46/3.18  tff('#skF_6', type, '#skF_6': $i).
% 9.46/3.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.46/3.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.46/3.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.46/3.18  tff('#skF_9', type, '#skF_9': $i).
% 9.46/3.18  tff('#skF_8', type, '#skF_8': $i).
% 9.46/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.46/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.46/3.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.46/3.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.46/3.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.46/3.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.46/3.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.46/3.18  
% 9.84/3.21  tff(f_77, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.84/3.21  tff(f_106, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 9.84/3.21  tff(f_70, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.84/3.21  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.84/3.21  tff(f_98, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 9.84/3.21  tff(f_68, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.84/3.21  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 9.84/3.21  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.84/3.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.84/3.21  tff(f_66, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.84/3.21  tff(c_32, plain, (![C_24]: (r2_hidden(C_24, k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.84/3.21  tff(c_66, plain, ('#skF_7'!='#skF_5' | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.84/3.21  tff(c_130, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_66])).
% 9.84/3.21  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.84/3.21  tff(c_210, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_68])).
% 9.84/3.21  tff(c_28, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.84/3.21  tff(c_305, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, B_94) | ~r2_hidden(C_95, A_93))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_324, plain, (![C_96, B_97, A_98]: (~r2_hidden(C_96, B_97) | ~r2_hidden(C_96, k4_xboole_0(A_98, B_97)))), inference(resolution, [status(thm)], [c_28, c_305])).
% 9.84/3.21  tff(c_336, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_210, c_324])).
% 9.84/3.21  tff(c_56, plain, (![B_49, A_48]: (k3_xboole_0(B_49, k1_tarski(A_48))=k1_tarski(A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.84/3.21  tff(c_60, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.84/3.21  tff(c_129, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_60])).
% 9.84/3.21  tff(c_26, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.84/3.21  tff(c_1604, plain, (![A_2218, B_2219, C_2220]: (r2_hidden(A_2218, B_2219) | r2_hidden(A_2218, C_2220) | ~r2_hidden(A_2218, k5_xboole_0(B_2219, C_2220)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.21  tff(c_4578, plain, (![A_4796, A_4797, B_4798]: (r2_hidden(A_4796, A_4797) | r2_hidden(A_4796, k3_xboole_0(A_4797, B_4798)) | ~r2_hidden(A_4796, k4_xboole_0(A_4797, B_4798)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1604])).
% 9.84/3.21  tff(c_4595, plain, (r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(resolution, [status(thm)], [c_210, c_4578])).
% 9.84/3.21  tff(c_4610, plain, (r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_129, c_4595])).
% 9.84/3.21  tff(c_4680, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10')) | ~r2_hidden('#skF_10', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_56, c_4610])).
% 9.84/3.21  tff(c_4689, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_336, c_4680])).
% 9.84/3.21  tff(c_54, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), B_47) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.84/3.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.84/3.21  tff(c_131, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.84/3.21  tff(c_134, plain, (![A_1, B_2, C_64]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_64, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 9.84/3.21  tff(c_4686, plain, (~r1_xboole_0(k1_tarski('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_4610, c_134])).
% 9.84/3.21  tff(c_4706, plain, (r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_54, c_4686])).
% 9.84/3.21  tff(c_4712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4689, c_4706])).
% 9.84/3.21  tff(c_4713, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 9.84/3.21  tff(c_5997, plain, (![A_7012, C_7013, B_7014]: (r2_hidden(A_7012, C_7013) | ~r2_hidden(A_7012, B_7014) | r2_hidden(A_7012, k5_xboole_0(B_7014, C_7013)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.21  tff(c_9624, plain, (![A_9816, A_9817, B_9818]: (r2_hidden(A_9816, k3_xboole_0(A_9817, B_9818)) | ~r2_hidden(A_9816, A_9817) | r2_hidden(A_9816, k4_xboole_0(A_9817, B_9818)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5997])).
% 9.84/3.21  tff(c_4714, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_68])).
% 9.84/3.21  tff(c_64, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.84/3.21  tff(c_4762, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_4714, c_64])).
% 9.84/3.21  tff(c_9672, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_9624, c_4762])).
% 9.84/3.21  tff(c_9697, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_4713, c_9672])).
% 9.84/3.21  tff(c_5981, plain, (![A_6967, B_6968, C_6969]: (r2_hidden(A_6967, B_6968) | ~r2_hidden(A_6967, C_6969) | r2_hidden(A_6967, k5_xboole_0(B_6968, C_6969)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.21  tff(c_5994, plain, (![A_6967, A_16, B_17]: (r2_hidden(A_6967, A_16) | ~r2_hidden(A_6967, k3_xboole_0(A_16, B_17)) | r2_hidden(A_6967, k4_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5981])).
% 9.84/3.21  tff(c_18, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_4810, plain, (![A_4984, B_4985, C_4986]: (~r1_xboole_0(A_4984, B_4985) | ~r2_hidden(C_4986, B_4985) | ~r2_hidden(C_4986, A_4984))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_5880, plain, (![C_6702, B_6703, A_6704]: (~r2_hidden(C_6702, B_6703) | ~r2_hidden(C_6702, k1_tarski(A_6704)) | r2_hidden(A_6704, B_6703))), inference(resolution, [status(thm)], [c_54, c_4810])).
% 9.84/3.21  tff(c_5928, plain, (![C_6835, A_6836]: (~r2_hidden(C_6835, k1_tarski(A_6836)) | r2_hidden(A_6836, k1_tarski(C_6835)))), inference(resolution, [status(thm)], [c_32, c_5880])).
% 9.84/3.21  tff(c_6759, plain, (![A_8022, A_8023]: (r2_hidden(A_8022, k1_tarski('#skF_1'(A_8023, k1_tarski(A_8022)))) | r1_xboole_0(A_8023, k1_tarski(A_8022)))), inference(resolution, [status(thm)], [c_18, c_5928])).
% 9.84/3.21  tff(c_5895, plain, (![A_6704]: (~r2_hidden('#skF_5', k1_tarski(A_6704)) | r2_hidden(A_6704, '#skF_6'))), inference(resolution, [status(thm)], [c_4713, c_5880])).
% 9.84/3.21  tff(c_6916, plain, (![A_8023]: (r2_hidden('#skF_1'(A_8023, k1_tarski('#skF_5')), '#skF_6') | r1_xboole_0(A_8023, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_6759, c_5895])).
% 9.84/3.21  tff(c_20, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_4890, plain, (![C_4999, B_5000, A_5001]: (~r2_hidden(C_4999, B_5000) | ~r2_hidden(C_4999, k4_xboole_0(A_5001, B_5000)))), inference(resolution, [status(thm)], [c_28, c_4810])).
% 9.84/3.21  tff(c_9210, plain, (![A_9166, B_9167, B_9168]: (~r2_hidden('#skF_1'(k4_xboole_0(A_9166, B_9167), B_9168), B_9167) | r1_xboole_0(k4_xboole_0(A_9166, B_9167), B_9168))), inference(resolution, [status(thm)], [c_20, c_4890])).
% 9.84/3.21  tff(c_9347, plain, (![A_9298]: (r1_xboole_0(k4_xboole_0(A_9298, '#skF_6'), k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_6916, c_9210])).
% 9.84/3.21  tff(c_4763, plain, (![B_4982, A_4983]: (k3_xboole_0(B_4982, k1_tarski(A_4983))=k1_tarski(A_4983) | ~r2_hidden(A_4983, B_4982))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.84/3.21  tff(c_153, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), B_68) | r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_24, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, k3_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.84/3.21  tff(c_162, plain, (![A_11, B_12, A_67]: (~r1_xboole_0(A_11, B_12) | r1_xboole_0(A_67, k3_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_153, c_24])).
% 9.84/3.21  tff(c_4784, plain, (![B_4982, A_4983, A_67]: (~r1_xboole_0(B_4982, k1_tarski(A_4983)) | r1_xboole_0(A_67, k1_tarski(A_4983)) | ~r2_hidden(A_4983, B_4982))), inference(superposition, [status(thm), theory('equality')], [c_4763, c_162])).
% 9.84/3.21  tff(c_9409, plain, (![A_67, A_9298]: (r1_xboole_0(A_67, k1_tarski('#skF_5')) | ~r2_hidden('#skF_5', k4_xboole_0(A_9298, '#skF_6')))), inference(resolution, [status(thm)], [c_9347, c_4784])).
% 9.84/3.21  tff(c_9589, plain, (![A_9687]: (~r2_hidden('#skF_5', k4_xboole_0(A_9687, '#skF_6')))), inference(splitLeft, [status(thm)], [c_9409])).
% 9.84/3.21  tff(c_9596, plain, (![A_9730]: (r2_hidden('#skF_5', A_9730) | ~r2_hidden('#skF_5', k3_xboole_0(A_9730, '#skF_6')))), inference(resolution, [status(thm)], [c_5994, c_9589])).
% 9.84/3.21  tff(c_9605, plain, (![A_1]: (r2_hidden('#skF_5', A_1) | ~r2_hidden('#skF_5', k3_xboole_0('#skF_6', A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9596])).
% 9.84/3.21  tff(c_9769, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_9697, c_9605])).
% 9.84/3.21  tff(c_30, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.84/3.21  tff(c_9836, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_9769, c_30])).
% 9.84/3.21  tff(c_9899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_9836])).
% 9.84/3.21  tff(c_9904, plain, (![A_10071]: (r1_xboole_0(A_10071, k1_tarski('#skF_5')))), inference(splitRight, [status(thm)], [c_9409])).
% 9.84/3.21  tff(c_4790, plain, (![B_4982, A_4983, C_15]: (~r1_xboole_0(B_4982, k1_tarski(A_4983)) | ~r2_hidden(C_15, k1_tarski(A_4983)) | ~r2_hidden(A_4983, B_4982))), inference(superposition, [status(thm), theory('equality')], [c_4763, c_24])).
% 9.84/3.21  tff(c_9980, plain, (![C_15, A_10071]: (~r2_hidden(C_15, k1_tarski('#skF_5')) | ~r2_hidden('#skF_5', A_10071))), inference(resolution, [status(thm)], [c_9904, c_4790])).
% 9.84/3.21  tff(c_10092, plain, (![A_10071]: (~r2_hidden('#skF_5', A_10071))), inference(splitLeft, [status(thm)], [c_9980])).
% 9.84/3.21  tff(c_10094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10092, c_4713])).
% 9.84/3.21  tff(c_10096, plain, (![C_10202]: (~r2_hidden(C_10202, k1_tarski('#skF_5')))), inference(splitRight, [status(thm)], [c_9980])).
% 9.84/3.21  tff(c_10122, plain, $false, inference(resolution, [status(thm)], [c_32, c_10096])).
% 9.84/3.21  tff(c_10123, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_66])).
% 9.84/3.21  tff(c_10242, plain, (![A_10268, B_10269, C_10270]: (~r1_xboole_0(A_10268, B_10269) | ~r2_hidden(C_10270, B_10269) | ~r2_hidden(C_10270, A_10268))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_10258, plain, (![C_10271, B_10272, A_10273]: (~r2_hidden(C_10271, B_10272) | ~r2_hidden(C_10271, k4_xboole_0(A_10273, B_10272)))), inference(resolution, [status(thm)], [c_28, c_10242])).
% 9.84/3.21  tff(c_10272, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_10123, c_10258])).
% 9.84/3.21  tff(c_10479, plain, (![A_10299, B_10300, C_10301]: (r2_hidden(A_10299, B_10300) | r2_hidden(A_10299, C_10301) | ~r2_hidden(A_10299, k5_xboole_0(B_10300, C_10301)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.21  tff(c_14183, plain, (![A_14624, A_14625, B_14626]: (r2_hidden(A_14624, A_14625) | r2_hidden(A_14624, k3_xboole_0(A_14625, B_14626)) | ~r2_hidden(A_14624, k4_xboole_0(A_14625, B_14626)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_10479])).
% 9.84/3.21  tff(c_14208, plain, (r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(resolution, [status(thm)], [c_10123, c_14183])).
% 9.84/3.21  tff(c_14216, plain, (r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_129, c_14208])).
% 9.84/3.21  tff(c_14287, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10')) | ~r2_hidden('#skF_10', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_56, c_14216])).
% 9.84/3.21  tff(c_14298, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_10272, c_14287])).
% 9.84/3.21  tff(c_10158, plain, (![A_10251, B_10252, C_10253]: (~r1_xboole_0(A_10251, B_10252) | ~r2_hidden(C_10253, k3_xboole_0(A_10251, B_10252)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.84/3.21  tff(c_10172, plain, (![B_2, A_1, C_10253]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_10253, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10158])).
% 9.84/3.21  tff(c_14294, plain, (~r1_xboole_0(k1_tarski('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_14216, c_10172])).
% 9.84/3.21  tff(c_14315, plain, (r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_54, c_14294])).
% 9.84/3.21  tff(c_14321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14298, c_14315])).
% 9.84/3.21  tff(c_14322, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 9.84/3.21  tff(c_14330, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_14322])).
% 9.84/3.21  tff(c_14323, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_60])).
% 9.84/3.21  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.84/3.21  tff(c_14324, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_62])).
% 9.84/3.21  tff(c_14326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14323, c_14324])).
% 9.84/3.21  tff(c_14327, plain, ('#skF_10'='#skF_8' | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 9.84/3.21  tff(c_14331, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_14327])).
% 9.84/3.21  tff(c_14681, plain, (![A_14851, C_14852, B_14853]: (r2_hidden(A_14851, C_14852) | ~r2_hidden(A_14851, B_14853) | r2_hidden(A_14851, k5_xboole_0(B_14853, C_14852)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.21  tff(c_17891, plain, (![A_19225, A_19226, B_19227]: (r2_hidden(A_19225, k3_xboole_0(A_19226, B_19227)) | ~r2_hidden(A_19225, A_19226) | r2_hidden(A_19225, k4_xboole_0(A_19226, B_19227)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_14681])).
% 9.84/3.21  tff(c_58, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.84/3.21  tff(c_14526, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_14323, c_58])).
% 9.84/3.21  tff(c_14527, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(splitLeft, [status(thm)], [c_14526])).
% 9.84/3.21  tff(c_17944, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_17891, c_14527])).
% 9.84/3.21  tff(c_17964, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_14331, c_17944])).
% 9.84/3.21  tff(c_14780, plain, (![A_14868, B_14869, C_14870]: (r2_hidden(A_14868, B_14869) | ~r2_hidden(A_14868, C_14870) | r2_hidden(A_14868, k5_xboole_0(B_14869, C_14870)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.21  tff(c_17501, plain, (![A_18568, A_18569, B_18570]: (r2_hidden(A_18568, A_18569) | ~r2_hidden(A_18568, k3_xboole_0(A_18569, B_18570)) | r2_hidden(A_18568, k4_xboole_0(A_18569, B_18570)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_14780])).
% 9.84/3.21  tff(c_14602, plain, (![A_14838, B_14839]: (r2_hidden('#skF_2'(A_14838, B_14839), k3_xboole_0(A_14838, B_14839)) | r1_xboole_0(A_14838, B_14839))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.84/3.21  tff(c_14338, plain, (![A_14797, B_14798, C_14799]: (~r1_xboole_0(A_14797, B_14798) | ~r2_hidden(C_14799, k3_xboole_0(A_14797, B_14798)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.84/3.21  tff(c_14345, plain, (![A_1, B_2, C_14799]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_14799, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14338])).
% 9.84/3.21  tff(c_14623, plain, (![B_14840, A_14841]: (~r1_xboole_0(B_14840, A_14841) | r1_xboole_0(A_14841, B_14840))), inference(resolution, [status(thm)], [c_14602, c_14345])).
% 9.84/3.21  tff(c_14648, plain, (![B_14842, A_14843]: (r1_xboole_0(B_14842, k4_xboole_0(A_14843, B_14842)))), inference(resolution, [status(thm)], [c_28, c_14623])).
% 9.84/3.21  tff(c_16, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_14655, plain, (![C_10, A_14843, B_14842]: (~r2_hidden(C_10, k4_xboole_0(A_14843, B_14842)) | ~r2_hidden(C_10, B_14842))), inference(resolution, [status(thm)], [c_14648, c_16])).
% 9.84/3.21  tff(c_17817, plain, (![A_19135, B_19136, A_19137]: (~r2_hidden(A_19135, B_19136) | r2_hidden(A_19135, A_19137) | ~r2_hidden(A_19135, k3_xboole_0(A_19137, B_19136)))), inference(resolution, [status(thm)], [c_17501, c_14655])).
% 9.84/3.21  tff(c_17845, plain, (![A_19135, B_2, A_1]: (~r2_hidden(A_19135, B_2) | r2_hidden(A_19135, A_1) | ~r2_hidden(A_19135, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17817])).
% 9.84/3.21  tff(c_17967, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_17964, c_17845])).
% 9.84/3.21  tff(c_18040, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_14331, c_17967])).
% 9.84/3.21  tff(c_18151, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_18040, c_30])).
% 9.84/3.21  tff(c_18211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14330, c_18151])).
% 9.84/3.21  tff(c_18212, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_14526])).
% 9.84/3.21  tff(c_18213, plain, (r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(splitRight, [status(thm)], [c_14526])).
% 9.84/3.21  tff(c_18279, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_18212, c_18213, c_64])).
% 9.84/3.21  tff(c_14506, plain, (![A_14826, B_14827, C_14828]: (~r1_xboole_0(A_14826, B_14827) | ~r2_hidden(C_14828, B_14827) | ~r2_hidden(C_14828, A_14826))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_14524, plain, (![C_14828, B_19, A_18]: (~r2_hidden(C_14828, B_19) | ~r2_hidden(C_14828, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_28, c_14506])).
% 9.84/3.21  tff(c_18282, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_18279, c_14524])).
% 9.84/3.21  tff(c_18286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_18282])).
% 9.84/3.21  tff(c_18288, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_14327])).
% 9.84/3.21  tff(c_18287, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_14327])).
% 9.84/3.21  tff(c_18366, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_18287, c_68])).
% 9.84/3.21  tff(c_18367, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_18288, c_18366])).
% 9.84/3.21  tff(c_18471, plain, (![A_19563, B_19564, C_19565]: (~r1_xboole_0(A_19563, B_19564) | ~r2_hidden(C_19565, B_19564) | ~r2_hidden(C_19565, A_19563))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_18490, plain, (![C_19566, B_19567, A_19568]: (~r2_hidden(C_19566, B_19567) | ~r2_hidden(C_19566, k4_xboole_0(A_19568, B_19567)))), inference(resolution, [status(thm)], [c_28, c_18471])).
% 9.84/3.21  tff(c_18493, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_18367, c_18490])).
% 9.84/3.21  tff(c_18505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_18493])).
% 9.84/3.21  tff(c_18506, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_14322])).
% 9.84/3.21  tff(c_18507, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_14322])).
% 9.84/3.21  tff(c_18533, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_18506, c_18507, c_66])).
% 9.84/3.21  tff(c_18639, plain, (![A_19595, B_19596, C_19597]: (~r1_xboole_0(A_19595, B_19596) | ~r2_hidden(C_19597, B_19596) | ~r2_hidden(C_19597, A_19595))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.21  tff(c_18658, plain, (![C_19598, B_19599, A_19600]: (~r2_hidden(C_19598, B_19599) | ~r2_hidden(C_19598, k4_xboole_0(A_19600, B_19599)))), inference(resolution, [status(thm)], [c_28, c_18639])).
% 9.84/3.21  tff(c_18669, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_18533, c_18658])).
% 9.84/3.21  tff(c_18675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_18669])).
% 9.84/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.21  
% 9.84/3.21  Inference rules
% 9.84/3.21  ----------------------
% 9.84/3.21  #Ref     : 0
% 9.84/3.21  #Sup     : 2914
% 9.84/3.21  #Fact    : 0
% 9.84/3.21  #Define  : 0
% 9.84/3.21  #Split   : 39
% 9.84/3.21  #Chain   : 0
% 9.84/3.21  #Close   : 0
% 9.84/3.21  
% 9.84/3.21  Ordering : KBO
% 9.84/3.21  
% 9.84/3.21  Simplification rules
% 9.84/3.21  ----------------------
% 9.84/3.21  #Subsume      : 616
% 9.84/3.21  #Demod        : 259
% 9.84/3.21  #Tautology    : 380
% 9.84/3.21  #SimpNegUnit  : 16
% 9.84/3.21  #BackRed      : 1
% 9.84/3.21  
% 9.84/3.21  #Partial instantiations: 8880
% 9.84/3.21  #Strategies tried      : 1
% 9.84/3.21  
% 9.84/3.21  Timing (in seconds)
% 9.84/3.21  ----------------------
% 9.84/3.21  Preprocessing        : 0.33
% 9.84/3.21  Parsing              : 0.17
% 9.84/3.21  CNF conversion       : 0.02
% 9.84/3.21  Main loop            : 2.10
% 9.84/3.21  Inferencing          : 0.95
% 9.84/3.21  Reduction            : 0.48
% 9.84/3.21  Demodulation         : 0.33
% 9.84/3.21  BG Simplification    : 0.09
% 9.84/3.21  Subsumption          : 0.43
% 9.84/3.21  Abstraction          : 0.09
% 9.84/3.21  MUC search           : 0.00
% 9.84/3.21  Cooper               : 0.00
% 9.84/3.21  Total                : 2.47
% 9.84/3.21  Index Insertion      : 0.00
% 9.84/3.21  Index Deletion       : 0.00
% 9.84/3.21  Index Matching       : 0.00
% 9.84/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
