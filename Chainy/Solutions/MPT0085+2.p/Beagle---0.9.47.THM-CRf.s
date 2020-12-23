%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0085+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 36.94s
% Output     : CNFRefutation 36.94s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 101 expanded)
%              Number of leaves         :   50 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 (  88 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_23 > #skF_8 > #skF_16 > #skF_15

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

tff('#skF_23',type,(
    '#skF_23': $i )).

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

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_546,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_404,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_396,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_317,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_270,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_426,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_615,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_342,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_498,plain,(
    ! [A_317] :
      ( k1_xboole_0 = A_317
      | ~ v1_xboole_0(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_505,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_498])).

tff(c_288,plain,(
    ! [A_185] : k4_xboole_0(A_185,k1_xboole_0) = A_185 ),
    inference(cnfTransformation,[status(thm)],[f_404])).

tff(c_509,plain,(
    ! [A_185] : k4_xboole_0(A_185,'#skF_9') = A_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_288])).

tff(c_280,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_396])).

tff(c_1826,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_280])).

tff(c_234,plain,(
    ! [A_124] : k2_xboole_0(A_124,k1_xboole_0) = A_124 ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_511,plain,(
    ! [A_124] : k2_xboole_0(A_124,'#skF_9') = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_234])).

tff(c_2862,plain,(
    ! [A_434,C_435,B_436] :
      ( r1_tarski(A_434,k2_xboole_0(C_435,B_436))
      | ~ r1_tarski(A_434,B_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_2953,plain,(
    ! [A_439,A_440] :
      ( r1_tarski(A_439,A_440)
      | ~ r1_tarski(A_439,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_2862])).

tff(c_2956,plain,(
    ! [A_179,A_440] :
      ( r1_tarski(A_179,A_440)
      | k4_xboole_0(A_179,'#skF_9') != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1826,c_2953])).

tff(c_2986,plain,(
    ! [A_441,A_442] :
      ( r1_tarski(A_441,A_442)
      | A_441 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_2956])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_399,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,B_202) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_3833,plain,(
    ! [A_442] : k2_xboole_0('#skF_9',A_442) = A_442 ),
    inference(resolution,[status(thm)],[c_2986,c_399])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_386,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_615])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1364,plain,(
    ! [A_384,B_385] :
      ( k3_xboole_0(A_384,B_385) = '#skF_9'
      | ~ r1_xboole_0(A_384,B_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_80])).

tff(c_1386,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_386,c_1364])).

tff(c_39654,plain,(
    ! [A_1049,B_1050,C_1051] : k2_xboole_0(k3_xboole_0(A_1049,B_1050),k3_xboole_0(A_1049,C_1051)) = k3_xboole_0(A_1049,k2_xboole_0(B_1050,C_1051)) ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_40048,plain,(
    ! [B_1050] : k3_xboole_0('#skF_21',k2_xboole_0(B_1050,'#skF_22')) = k2_xboole_0(k3_xboole_0('#skF_21',B_1050),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1386,c_39654])).

tff(c_40165,plain,(
    ! [B_1050] : k3_xboole_0('#skF_21',k2_xboole_0(B_1050,'#skF_22')) = k3_xboole_0('#skF_21',B_1050) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3833,c_6,c_40048])).

tff(c_384,plain,(
    k3_xboole_0('#skF_21',k2_xboole_0('#skF_22','#skF_23')) != k3_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_615])).

tff(c_407,plain,(
    k3_xboole_0('#skF_21',k2_xboole_0('#skF_22','#skF_23')) != k3_xboole_0('#skF_23','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_384])).

tff(c_408,plain,(
    k3_xboole_0('#skF_21',k2_xboole_0('#skF_23','#skF_22')) != k3_xboole_0('#skF_23','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_407])).

tff(c_129887,plain,(
    k3_xboole_0('#skF_21','#skF_23') != k3_xboole_0('#skF_23','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40165,c_408])).

tff(c_129890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_129887])).
%------------------------------------------------------------------------------
