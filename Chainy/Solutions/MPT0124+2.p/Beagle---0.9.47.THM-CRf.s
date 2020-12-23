%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0124+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:15 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :   59 (  60 expanded)
%              Number of leaves         :   45 (  46 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_22 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_23 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

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

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_23',type,(
    '#skF_23': ( $i * ( $i * $i ) ) > $i )).

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

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

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

tff(f_361,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(C,B)
       => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_493,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_517,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_429,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_523,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_535,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_274,plain,(
    r1_tarski('#skF_21','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_361])).

tff(c_350,plain,(
    ! [A_239,B_240] : k2_xboole_0(A_239,k4_xboole_0(B_240,A_239)) = k2_xboole_0(A_239,B_240) ),
    inference(cnfTransformation,[status(thm)],[f_493])).

tff(c_366,plain,(
    ! [A_257,B_258] :
      ( k2_xboole_0(A_257,k4_xboole_0(B_258,A_257)) = B_258
      | ~ r1_tarski(A_257,B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_517])).

tff(c_2752,plain,(
    ! [A_557,B_558] :
      ( k2_xboole_0(A_557,B_558) = B_558
      | ~ r1_tarski(A_557,B_558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_366])).

tff(c_2792,plain,(
    k2_xboole_0('#skF_21','#skF_20') = '#skF_20' ),
    inference(resolution,[status(thm)],[c_274,c_2752])).

tff(c_308,plain,(
    ! [A_188,B_189] : k3_xboole_0(A_188,k2_xboole_0(A_188,B_189)) = A_188 ),
    inference(cnfTransformation,[status(thm)],[f_429])).

tff(c_2822,plain,(
    k3_xboole_0('#skF_21','#skF_20') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_2792,c_308])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_372,plain,(
    ! [A_263,B_264] : k4_xboole_0(A_263,k4_xboole_0(A_263,B_264)) = k3_xboole_0(A_263,B_264) ),
    inference(cnfTransformation,[status(thm)],[f_523])).

tff(c_384,plain,(
    ! [A_277,B_278,C_279] : k2_xboole_0(k4_xboole_0(A_277,B_278),k3_xboole_0(A_277,C_279)) = k4_xboole_0(A_277,k4_xboole_0(B_278,C_279)) ),
    inference(cnfTransformation,[status(thm)],[f_535])).

tff(c_272,plain,(
    k2_xboole_0(k4_xboole_0('#skF_19','#skF_20'),k3_xboole_0('#skF_19',k4_xboole_0('#skF_20','#skF_21'))) != k4_xboole_0('#skF_19','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_361])).

tff(c_513,plain,(
    k4_xboole_0('#skF_19',k3_xboole_0('#skF_20','#skF_21')) != k4_xboole_0('#skF_19','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_384,c_272])).

tff(c_527,plain,(
    k4_xboole_0('#skF_19',k3_xboole_0('#skF_21','#skF_20')) != k4_xboole_0('#skF_19','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_513])).

tff(c_2881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_527])).
%------------------------------------------------------------------------------
