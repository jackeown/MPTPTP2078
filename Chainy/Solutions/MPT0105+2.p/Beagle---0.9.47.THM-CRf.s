%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0105+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:14 EST 2020

% Result     : Theorem 25.61s
% Output     : CNFRefutation 25.73s
% Verified   : 
% Statistics : Number of formulae       :   63 (  71 expanded)
%              Number of leaves         :   45 (  49 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_406,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_622,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_643,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

tff(f_270,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_454,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_708,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_290,plain,(
    ! [A_187,B_188] : k2_xboole_0(A_187,k4_xboole_0(B_188,A_187)) = k2_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_406])).

tff(c_392,plain,(
    ! [A_302,B_303] : r1_xboole_0(k4_xboole_0(A_302,B_303),B_303) ),
    inference(cnfTransformation,[status(thm)],[f_622])).

tff(c_740,plain,(
    ! [B_395,A_396] :
      ( r1_xboole_0(B_395,A_396)
      | ~ r1_xboole_0(A_396,B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_749,plain,(
    ! [B_303,A_302] : r1_xboole_0(B_303,k4_xboole_0(A_302,B_303)) ),
    inference(resolution,[status(thm)],[c_392,c_740])).

tff(c_1761,plain,(
    ! [A_456,B_457] :
      ( k4_xboole_0(A_456,B_457) = A_456
      | ~ r1_xboole_0(A_456,B_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_643])).

tff(c_1778,plain,(
    ! [B_303,A_302] : k4_xboole_0(B_303,k4_xboole_0(A_302,B_303)) = B_303 ),
    inference(resolution,[status(thm)],[c_749,c_1761])).

tff(c_10,plain,(
    ! [B_10,A_9] : k5_xboole_0(B_10,A_9) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40133,plain,(
    ! [A_1362,B_1363] : k4_xboole_0(k4_xboole_0(A_1362,B_1363),B_1363) = k4_xboole_0(A_1362,B_1363) ),
    inference(resolution,[status(thm)],[c_392,c_1761])).

tff(c_212,plain,(
    ! [A_97,B_98] : k4_xboole_0(k2_xboole_0(A_97,B_98),k3_xboole_0(A_97,B_98)) = k5_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_330,plain,(
    ! [A_234,B_235] : k4_xboole_0(k2_xboole_0(A_234,B_235),k3_xboole_0(A_234,B_235)) = k2_xboole_0(k4_xboole_0(A_234,B_235),k4_xboole_0(B_235,A_234)) ),
    inference(cnfTransformation,[status(thm)],[f_454])).

tff(c_451,plain,(
    ! [A_234,B_235] : k2_xboole_0(k4_xboole_0(A_234,B_235),k4_xboole_0(B_235,A_234)) = k5_xboole_0(A_234,B_235) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_330])).

tff(c_40211,plain,(
    ! [A_1362,B_1363] : k2_xboole_0(k4_xboole_0(A_1362,B_1363),k4_xboole_0(B_1363,k4_xboole_0(A_1362,B_1363))) = k5_xboole_0(k4_xboole_0(A_1362,B_1363),B_1363) ),
    inference(superposition,[status(thm),theory(equality)],[c_40133,c_451])).

tff(c_40488,plain,(
    ! [B_1363,A_1362] : k5_xboole_0(B_1363,k4_xboole_0(A_1362,B_1363)) = k2_xboole_0(B_1363,A_1362) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_6,c_1778,c_10,c_40211])).

tff(c_440,plain,(
    k5_xboole_0('#skF_21',k4_xboole_0('#skF_22','#skF_21')) != k2_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_708])).

tff(c_457,plain,(
    k5_xboole_0('#skF_21',k4_xboole_0('#skF_22','#skF_21')) != k2_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_440])).

tff(c_95070,plain,(
    k2_xboole_0('#skF_21','#skF_22') != k2_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40488,c_457])).

tff(c_95074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_95070])).
%------------------------------------------------------------------------------
