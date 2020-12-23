%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0020+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:10 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :   61 (  72 expanded)
%              Number of leaves         :   42 (  49 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  56 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

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

tff(f_273,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_266,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_304,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_262,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_318,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_210,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_623,plain,(
    ! [A_166,B_167] :
      ( k2_xboole_0(A_166,B_167) = B_167
      | ~ r1_tarski(A_166,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_647,plain,(
    k2_xboole_0('#skF_21','#skF_22') = '#skF_22' ),
    inference(resolution,[status(thm)],[c_210,c_623])).

tff(c_232,plain,(
    ! [A_112,B_113] : r1_tarski(A_112,k2_xboole_0(A_112,B_113)) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_2584,plain,(
    ! [A_317,C_318,B_319] :
      ( r1_tarski(A_317,C_318)
      | ~ r1_tarski(k2_xboole_0(A_317,B_319),C_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_2800,plain,(
    ! [A_324,B_325,B_326] : r1_tarski(A_324,k2_xboole_0(k2_xboole_0(A_324,B_325),B_326)) ),
    inference(resolution,[status(thm)],[c_232,c_2584])).

tff(c_2846,plain,(
    ! [B_326] : r1_tarski('#skF_21',k2_xboole_0('#skF_22',B_326)) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_2800])).

tff(c_362,plain,(
    ! [B_137,A_138] : k2_xboole_0(B_137,A_138) = k2_xboole_0(A_138,B_137) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_377,plain,(
    ! [A_138,B_137] : r1_tarski(A_138,k2_xboole_0(B_137,A_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_232])).

tff(c_212,plain,(
    r1_tarski('#skF_19','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_646,plain,(
    k2_xboole_0('#skF_19','#skF_20') = '#skF_20' ),
    inference(resolution,[status(thm)],[c_212,c_623])).

tff(c_2680,plain,(
    ! [C_321] :
      ( r1_tarski('#skF_19',C_321)
      | ~ r1_tarski('#skF_20',C_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_2584])).

tff(c_2708,plain,(
    ! [B_137] : r1_tarski('#skF_19',k2_xboole_0(B_137,'#skF_20')) ),
    inference(resolution,[status(thm)],[c_377,c_2680])).

tff(c_5478,plain,(
    ! [A_411,C_412,B_413] :
      ( r1_tarski(k2_xboole_0(A_411,C_412),B_413)
      | ~ r1_tarski(C_412,B_413)
      | ~ r1_tarski(A_411,B_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_208,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_19','#skF_21'),k2_xboole_0('#skF_20','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_243,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_21','#skF_19'),k2_xboole_0('#skF_22','#skF_20')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_208])).

tff(c_5523,plain,
    ( ~ r1_tarski('#skF_19',k2_xboole_0('#skF_22','#skF_20'))
    | ~ r1_tarski('#skF_21',k2_xboole_0('#skF_22','#skF_20')) ),
    inference(resolution,[status(thm)],[c_5478,c_243])).

tff(c_5583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2846,c_2708,c_5523])).
%------------------------------------------------------------------------------
