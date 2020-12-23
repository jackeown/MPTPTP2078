%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0028+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:10 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :   54 (  56 expanded)
%              Number of leaves         :   41 (  43 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  41 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_352,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_324,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_327,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_609,plain,(
    ! [B_190,A_191] : k2_xboole_0(B_190,A_191) = k2_xboole_0(A_191,B_190) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_254,plain,(
    ! [A_138,B_139] : r1_tarski(A_138,k2_xboole_0(A_138,B_139)) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_642,plain,(
    ! [A_191,B_190] : r1_tarski(A_191,k2_xboole_0(B_190,A_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_254])).

tff(c_196,plain,(
    ! [B_82] : r1_tarski(B_82,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_234,plain,(
    ! [A_120,B_121,C_122] :
      ( r1_tarski('#skF_20'(A_120,B_121,C_122),B_121)
      | k3_xboole_0(B_121,C_122) = A_120
      | ~ r1_tarski(A_120,C_122)
      | ~ r1_tarski(A_120,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_324])).

tff(c_7662,plain,(
    ! [A_541,B_542,C_543] :
      ( ~ r1_tarski('#skF_20'(A_541,B_542,C_543),A_541)
      | k3_xboole_0(B_542,C_543) = A_541
      | ~ r1_tarski(A_541,C_543)
      | ~ r1_tarski(A_541,B_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_324])).

tff(c_7666,plain,(
    ! [B_121,C_122] :
      ( k3_xboole_0(B_121,C_122) = B_121
      | ~ r1_tarski(B_121,C_122)
      | ~ r1_tarski(B_121,B_121) ) ),
    inference(resolution,[status(thm)],[c_234,c_7662])).

tff(c_7697,plain,(
    ! [B_544,C_545] :
      ( k3_xboole_0(B_544,C_545) = B_544
      | ~ r1_tarski(B_544,C_545) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_7666])).

tff(c_7811,plain,(
    ! [A_191,B_190] : k3_xboole_0(A_191,k2_xboole_0(B_190,A_191)) = A_191 ),
    inference(resolution,[status(thm)],[c_642,c_7697])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_236,plain,(
    k3_xboole_0('#skF_21',k2_xboole_0('#skF_21','#skF_22')) != '#skF_21' ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_265,plain,(
    k3_xboole_0('#skF_21',k2_xboole_0('#skF_22','#skF_21')) != '#skF_21' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_236])).

tff(c_7819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7811,c_265])).
%------------------------------------------------------------------------------
