%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0027+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:10 EST 2020

% Result     : Theorem 8.15s
% Output     : CNFRefutation 8.15s
% Verified   : 
% Statistics : Number of formulae       :   69 (  76 expanded)
%              Number of leaves         :   44 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 (  78 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_325,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & ! [D] :
              ( ( r1_tarski(D,B)
                & r1_tarski(D,C) )
             => r1_tarski(D,A) ) )
       => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_303,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_293,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_266,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_350,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_234,plain,(
    r1_tarski('#skF_20','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_236,plain,(
    r1_tarski('#skF_20','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_10685,plain,(
    ! [A_497,B_498,C_499] :
      ( r1_tarski(A_497,k3_xboole_0(B_498,C_499))
      | ~ r1_tarski(A_497,C_499)
      | ~ r1_tarski(A_497,B_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_230,plain,(
    k3_xboole_0('#skF_21','#skF_22') != '#skF_20' ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_265,plain,(
    k3_xboole_0('#skF_22','#skF_21') != '#skF_20' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_230])).

tff(c_220,plain,(
    ! [A_108,B_109] : r1_tarski(k3_xboole_0(A_108,B_109),A_108) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_450,plain,(
    ! [B_169,A_170] : k3_xboole_0(B_169,A_170) = k3_xboole_0(A_170,B_169) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_473,plain,(
    ! [B_169,A_170] : r1_tarski(k3_xboole_0(B_169,A_170),A_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_220])).

tff(c_232,plain,(
    ! [D_121] :
      ( r1_tarski(D_121,'#skF_20')
      | ~ r1_tarski(D_121,'#skF_22')
      | ~ r1_tarski(D_121,'#skF_21') ) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_785,plain,(
    ! [A_196,B_197] :
      ( k2_xboole_0(A_196,B_197) = B_197
      | ~ r1_tarski(A_196,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_917,plain,(
    ! [D_200] :
      ( k2_xboole_0(D_200,'#skF_20') = '#skF_20'
      | ~ r1_tarski(D_200,'#skF_22')
      | ~ r1_tarski(D_200,'#skF_21') ) ),
    inference(resolution,[status(thm)],[c_232,c_785])).

tff(c_921,plain,(
    ! [B_169] :
      ( k2_xboole_0(k3_xboole_0(B_169,'#skF_21'),'#skF_20') = '#skF_20'
      | ~ r1_tarski(k3_xboole_0(B_169,'#skF_21'),'#skF_22') ) ),
    inference(resolution,[status(thm)],[c_473,c_917])).

tff(c_1082,plain,(
    ! [B_209] :
      ( k2_xboole_0('#skF_20',k3_xboole_0(B_209,'#skF_21')) = '#skF_20'
      | ~ r1_tarski(k3_xboole_0(B_209,'#skF_21'),'#skF_22') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_921])).

tff(c_1105,plain,(
    k2_xboole_0('#skF_20',k3_xboole_0('#skF_22','#skF_21')) = '#skF_20' ),
    inference(resolution,[status(thm)],[c_220,c_1082])).

tff(c_574,plain,(
    ! [B_183,A_184] : k2_xboole_0(B_183,A_184) = k2_xboole_0(A_184,B_183) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_254,plain,(
    ! [A_136,B_137] : r1_tarski(A_136,k2_xboole_0(A_136,B_137)) ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_595,plain,(
    ! [A_184,B_183] : r1_tarski(A_184,k2_xboole_0(B_183,A_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_254])).

tff(c_1524,plain,(
    r1_tarski(k3_xboole_0('#skF_22','#skF_21'),'#skF_20') ),
    inference(superposition,[status(thm),theory(equality)],[c_1105,c_595])).

tff(c_5092,plain,(
    ! [B_349,A_350] :
      ( B_349 = A_350
      | ~ r1_tarski(B_349,A_350)
      | ~ r1_tarski(A_350,B_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_5112,plain,
    ( k3_xboole_0('#skF_22','#skF_21') = '#skF_20'
    | ~ r1_tarski('#skF_20',k3_xboole_0('#skF_22','#skF_21')) ),
    inference(resolution,[status(thm)],[c_1524,c_5092])).

tff(c_5140,plain,(
    ~ r1_tarski('#skF_20',k3_xboole_0('#skF_22','#skF_21')) ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_5112])).

tff(c_10712,plain,
    ( ~ r1_tarski('#skF_20','#skF_21')
    | ~ r1_tarski('#skF_20','#skF_22') ),
    inference(resolution,[status(thm)],[c_10685,c_5140])).

tff(c_10780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_236,c_10712])).
%------------------------------------------------------------------------------
