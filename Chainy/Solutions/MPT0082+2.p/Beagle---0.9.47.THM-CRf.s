%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0082+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   45 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 123 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_546,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_599,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

tff(f_604,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_305,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_542,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_427,plain,(
    ! [A_305] :
      ( k1_xboole_0 = A_305
      | ~ v1_xboole_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_436,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_427])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2180,plain,(
    ! [A_406,B_407] :
      ( r1_xboole_0(A_406,B_407)
      | k3_xboole_0(A_406,B_407) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_82])).

tff(c_380,plain,(
    ~ r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_599])).

tff(c_2192,plain,(
    k3_xboole_0('#skF_21','#skF_22') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_2180,c_380])).

tff(c_2198,plain,(
    k3_xboole_0('#skF_22','#skF_21') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2192])).

tff(c_378,plain,(
    r1_xboole_0(k3_xboole_0('#skF_21','#skF_22'),'#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_599])).

tff(c_401,plain,(
    r1_xboole_0(k3_xboole_0('#skF_22','#skF_21'),'#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_378])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1383,plain,(
    ! [A_374,B_375] :
      ( k3_xboole_0(A_374,B_375) = '#skF_9'
      | ~ r1_xboole_0(A_374,B_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_80])).

tff(c_1401,plain,(
    k3_xboole_0(k3_xboole_0('#skF_22','#skF_21'),'#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_401,c_1383])).

tff(c_2663,plain,(
    ! [D_421,A_422,B_423] :
      ( r2_hidden(D_421,A_422)
      | ~ r2_hidden(D_421,k3_xboole_0(A_422,B_423)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2793,plain,(
    ! [D_426] :
      ( r2_hidden(D_426,k3_xboole_0('#skF_22','#skF_21'))
      | ~ r2_hidden(D_426,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1401,c_2663])).

tff(c_382,plain,(
    ! [B_287,A_286] :
      ( ~ v1_xboole_0(B_287)
      | ~ r2_hidden(A_286,B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_604])).

tff(c_2810,plain,(
    ! [D_426] :
      ( ~ v1_xboole_0(k3_xboole_0('#skF_22','#skF_21'))
      | ~ r2_hidden(D_426,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2793,c_382])).

tff(c_3401,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_22','#skF_21')) ),
    inference(splitLeft,[status(thm)],[c_2810])).

tff(c_228,plain,(
    ! [A_116,B_117] : r1_tarski(k3_xboole_0(A_116,B_117),A_116) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_8291,plain,(
    ! [B_638,A_639] :
      ( ~ r1_xboole_0(B_638,A_639)
      | ~ r1_tarski(B_638,A_639)
      | v1_xboole_0(B_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_542])).

tff(c_8321,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_22','#skF_21'),'#skF_22')
    | v1_xboole_0(k3_xboole_0('#skF_22','#skF_21')) ),
    inference(resolution,[status(thm)],[c_401,c_8291])).

tff(c_8337,plain,(
    v1_xboole_0(k3_xboole_0('#skF_22','#skF_21')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_8321])).

tff(c_8339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3401,c_8337])).

tff(c_8341,plain,(
    v1_xboole_0(k3_xboole_0('#skF_22','#skF_21')) ),
    inference(splitRight,[status(thm)],[c_2810])).

tff(c_360,plain,(
    ! [A_267] :
      ( k1_xboole_0 = A_267
      | ~ v1_xboole_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_437,plain,(
    ! [A_267] :
      ( A_267 = '#skF_9'
      | ~ v1_xboole_0(A_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_360])).

tff(c_8365,plain,(
    k3_xboole_0('#skF_22','#skF_21') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_8341,c_437])).

tff(c_8379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2198,c_8365])).
%------------------------------------------------------------------------------
