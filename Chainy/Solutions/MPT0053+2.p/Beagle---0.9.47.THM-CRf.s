%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0053+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:11 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   56 (  62 expanded)
%              Number of leaves         :   42 (  45 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  33 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

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

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_440,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_431,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_388,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_421,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_651,plain,(
    ! [B_250,A_251] : k2_xboole_0(B_250,A_251) = k2_xboole_0(A_251,B_250) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_314,plain,(
    ! [A_209,B_210] : r1_tarski(A_209,k2_xboole_0(A_209,B_210)) ),
    inference(cnfTransformation,[status(thm)],[f_440])).

tff(c_672,plain,(
    ! [A_251,B_250] : r1_tarski(A_251,k2_xboole_0(B_250,A_251)) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_314])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_336,plain,(
    ! [A_222] :
      ( k1_xboole_0 = A_222
      | ~ v1_xboole_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_431])).

tff(c_345,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_336])).

tff(c_278,plain,(
    ! [A_173,B_174] :
      ( k4_xboole_0(A_173,B_174) = k1_xboole_0
      | ~ r1_tarski(A_173,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_388])).

tff(c_1495,plain,(
    ! [A_301,B_302] :
      ( k4_xboole_0(A_301,B_302) = '#skF_9'
      | ~ r1_tarski(A_301,B_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_278])).

tff(c_1525,plain,(
    ! [A_251,B_250] : k4_xboole_0(A_251,k2_xboole_0(B_250,A_251)) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_672,c_1495])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_300,plain,(
    k4_xboole_0('#skF_21',k2_xboole_0('#skF_21','#skF_22')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_421])).

tff(c_328,plain,(
    k4_xboole_0('#skF_21',k2_xboole_0('#skF_22','#skF_21')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_300])).

tff(c_355,plain,(
    k4_xboole_0('#skF_21',k2_xboole_0('#skF_22','#skF_21')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_328])).

tff(c_1564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_355])).
%------------------------------------------------------------------------------
