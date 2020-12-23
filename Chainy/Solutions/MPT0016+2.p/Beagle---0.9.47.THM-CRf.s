%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0016+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   53 (  60 expanded)
%              Number of leaves         :   40 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

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

tff('#skF_19',type,(
    '#skF_19': $i )).

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

tff(f_304,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_285,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_262,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_299,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_228,plain,(
    r1_tarski('#skF_19','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_220,plain,(
    ! [A_104,B_105] : r1_tarski(A_104,k2_xboole_0(A_104,B_105)) ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_1526,plain,(
    ! [A_250,C_251,B_252] :
      ( r1_tarski(A_250,C_251)
      | ~ r1_tarski(B_252,C_251)
      | ~ r1_tarski(A_250,B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_1811,plain,(
    ! [A_280,A_281,B_282] :
      ( r1_tarski(A_280,k2_xboole_0(A_281,B_282))
      | ~ r1_tarski(A_280,A_281) ) ),
    inference(resolution,[status(thm)],[c_220,c_1526])).

tff(c_4277,plain,(
    ! [A_418,A_419,B_420] :
      ( r1_tarski(A_418,k2_xboole_0(A_419,B_420))
      | ~ r1_tarski(A_418,B_420) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1811])).

tff(c_2727,plain,(
    ! [A_330,C_331,B_332] :
      ( r1_tarski(k2_xboole_0(A_330,C_331),B_332)
      | ~ r1_tarski(C_331,B_332)
      | ~ r1_tarski(A_330,B_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_226,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_19','#skF_21'),k2_xboole_0('#skF_20','#skF_21')) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_233,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_21','#skF_19'),k2_xboole_0('#skF_21','#skF_20')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_226])).

tff(c_2764,plain,
    ( ~ r1_tarski('#skF_19',k2_xboole_0('#skF_21','#skF_20'))
    | ~ r1_tarski('#skF_21',k2_xboole_0('#skF_21','#skF_20')) ),
    inference(resolution,[status(thm)],[c_2727,c_233])).

tff(c_2804,plain,(
    ~ r1_tarski('#skF_19',k2_xboole_0('#skF_21','#skF_20')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_2764])).

tff(c_4282,plain,(
    ~ r1_tarski('#skF_19','#skF_20') ),
    inference(resolution,[status(thm)],[c_4277,c_2804])).

tff(c_4332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_4282])).
%------------------------------------------------------------------------------
