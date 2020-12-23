%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0080+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 46.98s
% Output     : CNFRefutation 47.11s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 116 expanded)
%              Number of leaves         :   53 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :   75 ( 107 expanded)
%              Number of equality atoms :   45 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_587,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_410,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_340,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_301,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_430,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_440,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_305,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_442,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_270,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_374,plain,(
    ~ r1_tarski('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_587])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4510,plain,(
    ! [A_478,B_479] : k4_xboole_0(k2_xboole_0(A_478,B_479),B_479) = k4_xboole_0(A_478,B_479) ),
    inference(cnfTransformation,[status(thm)],[f_410])).

tff(c_4594,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),A_5) = k4_xboole_0(B_6,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4510])).

tff(c_378,plain,(
    r1_tarski('#skF_21',k2_xboole_0('#skF_22','#skF_23')) ),
    inference(cnfTransformation,[status(thm)],[f_587])).

tff(c_399,plain,(
    r1_tarski('#skF_21',k2_xboole_0('#skF_23','#skF_22')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_378])).

tff(c_1203,plain,(
    ! [A_362,B_363] :
      ( k3_xboole_0(A_362,B_363) = A_362
      | ~ r1_tarski(A_362,B_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_1238,plain,(
    k3_xboole_0('#skF_21',k2_xboole_0('#skF_23','#skF_22')) = '#skF_21' ),
    inference(resolution,[status(thm)],[c_399,c_1203])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_427,plain,(
    ! [A_299] :
      ( k1_xboole_0 = A_299
      | ~ v1_xboole_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_436,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_427])).

tff(c_288,plain,(
    ! [A_185] : k4_xboole_0(A_185,k1_xboole_0) = A_185 ),
    inference(cnfTransformation,[status(thm)],[f_404])).

tff(c_448,plain,(
    ! [A_185] : k4_xboole_0(A_185,'#skF_9') = A_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_288])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1091,plain,(
    ! [A_357,B_358] : k2_xboole_0(A_357,k3_xboole_0(A_357,B_358)) = A_357 ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_1125,plain,(
    ! [B_8,A_7] : k2_xboole_0(B_8,k3_xboole_0(A_7,B_8)) = B_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1091])).

tff(c_224,plain,(
    ! [A_111,B_112] :
      ( k1_xboole_0 = A_111
      | k2_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_873,plain,(
    ! [A_335,B_336] :
      ( A_335 = '#skF_9'
      | k2_xboole_0(A_335,B_336) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_436,c_224])).

tff(c_1511,plain,(
    ! [B_374,A_375] :
      ( B_374 = '#skF_9'
      | k2_xboole_0(A_375,B_374) != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_873])).

tff(c_1514,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = '#skF_9'
      | B_8 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_1511])).

tff(c_8053,plain,(
    ! [A_589,B_590] : k4_xboole_0(A_589,k3_xboole_0(A_589,B_590)) = k4_xboole_0(A_589,B_590) ),
    inference(cnfTransformation,[status(thm)],[f_430])).

tff(c_8142,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k4_xboole_0(A_7,'#skF_9')
      | B_8 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1514,c_8053])).

tff(c_8625,plain,(
    ! [A_7] : k4_xboole_0(A_7,'#skF_9') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_8142])).

tff(c_376,plain,(
    r1_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_587])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1572,plain,(
    ! [A_378,B_379] :
      ( k3_xboole_0(A_378,B_379) = '#skF_9'
      | ~ r1_xboole_0(A_378,B_379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_80])).

tff(c_1590,plain,(
    k3_xboole_0('#skF_21','#skF_23') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_376,c_1572])).

tff(c_36108,plain,(
    ! [A_1004,B_1005,C_1006] : k4_xboole_0(k3_xboole_0(A_1004,B_1005),k3_xboole_0(A_1004,C_1006)) = k3_xboole_0(A_1004,k4_xboole_0(B_1005,C_1006)) ),
    inference(cnfTransformation,[status(thm)],[f_440])).

tff(c_36430,plain,(
    ! [B_1005] : k4_xboole_0(k3_xboole_0('#skF_21',B_1005),'#skF_9') = k3_xboole_0('#skF_21',k4_xboole_0(B_1005,'#skF_23')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1590,c_36108])).

tff(c_174108,plain,(
    ! [B_2424] : k3_xboole_0('#skF_21',k4_xboole_0(B_2424,'#skF_23')) = k3_xboole_0('#skF_21',B_2424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8625,c_36430])).

tff(c_945,plain,(
    ! [B_347,A_348] : k3_xboole_0(B_347,A_348) = k3_xboole_0(A_348,B_347) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [A_116,B_117] : r1_tarski(k3_xboole_0(A_116,B_117),A_116) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_968,plain,(
    ! [B_347,A_348] : r1_tarski(k3_xboole_0(B_347,A_348),A_348) ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_228])).

tff(c_175050,plain,(
    ! [B_2429] : r1_tarski(k3_xboole_0('#skF_21',B_2429),k4_xboole_0(B_2429,'#skF_23')) ),
    inference(superposition,[status(thm),theory(equality)],[c_174108,c_968])).

tff(c_175220,plain,(
    r1_tarski('#skF_21',k4_xboole_0(k2_xboole_0('#skF_23','#skF_22'),'#skF_23')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_175050])).

tff(c_175289,plain,(
    r1_tarski('#skF_21',k4_xboole_0('#skF_22','#skF_23')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4594,c_175220])).

tff(c_8415,plain,(
    ! [A_592,B_593] : k2_xboole_0(k3_xboole_0(A_592,B_593),k4_xboole_0(A_592,B_593)) = A_592 ),
    inference(cnfTransformation,[status(thm)],[f_442])).

tff(c_210,plain,(
    ! [A_95,C_97,B_96] :
      ( r1_tarski(A_95,k2_xboole_0(C_97,B_96))
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_8424,plain,(
    ! [A_95,A_592,B_593] :
      ( r1_tarski(A_95,A_592)
      | ~ r1_tarski(A_95,k4_xboole_0(A_592,B_593)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8415,c_210])).

tff(c_175299,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(resolution,[status(thm)],[c_175289,c_8424])).

tff(c_175368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_175299])).
%------------------------------------------------------------------------------
