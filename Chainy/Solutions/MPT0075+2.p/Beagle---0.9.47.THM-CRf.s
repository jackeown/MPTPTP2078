%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0075+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 142 expanded)
%              Number of leaves         :   51 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 181 expanded)
%              Number of equality atoms :   35 (  62 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_535,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_539,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_199,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_340,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_xboole_0)).

tff(f_404,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_430,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d5_xboole_0)).

tff(c_362,plain,(
    ~ v1_xboole_0('#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_535])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | r2_hidden('#skF_1'(A_11),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_360,plain,(
    r1_tarski('#skF_23','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_535])).

tff(c_1924,plain,(
    ! [A_379,B_380] :
      ( k3_xboole_0(A_379,B_380) = A_379
      | ~ r1_tarski(A_379,B_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_1968,plain,(
    k3_xboole_0('#skF_23','#skF_21') = '#skF_23' ),
    inference(resolution,[status(thm)],[c_360,c_1924])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_476,plain,(
    ! [A_288] :
      ( k1_xboole_0 = A_288
      | ~ v1_xboole_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_485,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_476])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1297,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_82])).

tff(c_3713,plain,(
    ! [A_415,B_416,C_417] :
      ( ~ r1_xboole_0(A_415,B_416)
      | ~ r2_hidden(C_417,k3_xboole_0(A_415,B_416)) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_3719,plain,(
    ! [C_417] :
      ( ~ r1_xboole_0('#skF_23','#skF_21')
      | ~ r2_hidden(C_417,'#skF_23') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1968,c_3713])).

tff(c_3776,plain,(
    ~ r1_xboole_0('#skF_23','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_3719])).

tff(c_3779,plain,(
    k3_xboole_0('#skF_23','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1297,c_3776])).

tff(c_3781,plain,(
    '#skF_9' != '#skF_23' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_3779])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_1224,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_190])).

tff(c_358,plain,(
    r1_tarski('#skF_23','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_535])).

tff(c_1967,plain,(
    k3_xboole_0('#skF_23','#skF_22') = '#skF_23' ),
    inference(resolution,[status(thm)],[c_358,c_1924])).

tff(c_883,plain,(
    ! [B_331,A_332] : k3_xboole_0(B_331,A_332) = k3_xboole_0(A_332,B_331) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_246,plain,(
    ! [A_134,B_135] : k2_xboole_0(A_134,k3_xboole_0(A_134,B_135)) = A_134 ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_901,plain,(
    ! [B_331,A_332] : k2_xboole_0(B_331,k3_xboole_0(A_332,B_331)) = B_331 ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_246])).

tff(c_1987,plain,(
    k2_xboole_0('#skF_22','#skF_23') = '#skF_22' ),
    inference(superposition,[status(thm),theory(equality)],[c_1967,c_901])).

tff(c_3211,plain,(
    ! [D_402,B_403,A_404] :
      ( ~ r2_hidden(D_402,B_403)
      | r2_hidden(D_402,k2_xboole_0(A_404,B_403)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3240,plain,(
    ! [D_402] :
      ( ~ r2_hidden(D_402,'#skF_23')
      | r2_hidden(D_402,'#skF_22') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1987,c_3211])).

tff(c_2026,plain,(
    k2_xboole_0('#skF_21','#skF_23') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_1968,c_901])).

tff(c_3243,plain,(
    ! [D_402] :
      ( ~ r2_hidden(D_402,'#skF_23')
      | r2_hidden(D_402,'#skF_21') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2026,c_3211])).

tff(c_288,plain,(
    ! [A_185] : k4_xboole_0(A_185,k1_xboole_0) = A_185 ),
    inference(cnfTransformation,[status(thm)],[f_404])).

tff(c_487,plain,(
    ! [A_185] : k4_xboole_0(A_185,'#skF_9') = A_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_288])).

tff(c_356,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_535])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1395,plain,(
    ! [A_355,B_356] :
      ( k3_xboole_0(A_355,B_356) = '#skF_9'
      | ~ r1_xboole_0(A_355,B_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_80])).

tff(c_1417,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_356,c_1395])).

tff(c_4041,plain,(
    ! [A_429,B_430] : k4_xboole_0(A_429,k3_xboole_0(A_429,B_430)) = k4_xboole_0(A_429,B_430) ),
    inference(cnfTransformation,[status(thm)],[f_430])).

tff(c_4087,plain,(
    k4_xboole_0('#skF_21','#skF_9') = k4_xboole_0('#skF_21','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_4041])).

tff(c_4116,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_4087])).

tff(c_4932,plain,(
    ! [D_450,B_451,A_452] :
      ( ~ r2_hidden(D_450,B_451)
      | ~ r2_hidden(D_450,k4_xboole_0(A_452,B_451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5149,plain,(
    ! [D_456] :
      ( ~ r2_hidden(D_456,'#skF_22')
      | ~ r2_hidden(D_456,'#skF_21') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4116,c_4932])).

tff(c_5590,plain,(
    ! [D_476] :
      ( ~ r2_hidden(D_476,'#skF_22')
      | ~ r2_hidden(D_476,'#skF_23') ) ),
    inference(resolution,[status(thm)],[c_3243,c_5149])).

tff(c_5614,plain,(
    ! [D_477] : ~ r2_hidden(D_477,'#skF_23') ),
    inference(resolution,[status(thm)],[c_3240,c_5590])).

tff(c_5622,plain,(
    '#skF_9' = '#skF_23' ),
    inference(resolution,[status(thm)],[c_1224,c_5614])).

tff(c_5631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3781,c_5622])).

tff(c_5634,plain,(
    ! [C_478] : ~ r2_hidden(C_478,'#skF_23') ),
    inference(splitRight,[status(thm)],[c_3719])).

tff(c_5642,plain,(
    v1_xboole_0('#skF_23') ),
    inference(resolution,[status(thm)],[c_14,c_5634])).

tff(c_5647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_5642])).
%------------------------------------------------------------------------------
