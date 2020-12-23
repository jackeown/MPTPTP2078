%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0025+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:10 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :   57 (  61 expanded)
%              Number of leaves         :   42 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  47 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

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

tff(f_298,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k3_xboole_0(B,C))
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_266,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

tff(c_222,plain,(
    ~ r1_tarski('#skF_20','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_3461,plain,(
    ! [A_347,B_348] :
      ( r2_hidden('#skF_2'(A_347,B_348),A_347)
      | r1_tarski(A_347,B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_224,plain,(
    r1_tarski('#skF_20',k3_xboole_0('#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_257,plain,(
    r1_tarski('#skF_20',k3_xboole_0('#skF_22','#skF_21')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_224])).

tff(c_775,plain,(
    ! [A_189,B_190] :
      ( k2_xboole_0(A_189,B_190) = B_190
      | ~ r1_tarski(A_189,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_803,plain,(
    k2_xboole_0('#skF_20',k3_xboole_0('#skF_22','#skF_21')) = k3_xboole_0('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_257,c_775])).

tff(c_1598,plain,(
    ! [D_235,A_236,B_237] :
      ( ~ r2_hidden(D_235,A_236)
      | r2_hidden(D_235,k2_xboole_0(A_236,B_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1678,plain,(
    ! [D_243] :
      ( ~ r2_hidden(D_243,'#skF_20')
      | r2_hidden(D_243,k3_xboole_0('#skF_22','#skF_21')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_1598])).

tff(c_44,plain,(
    ! [D_31,B_27,A_26] :
      ( r2_hidden(D_31,B_27)
      | ~ r2_hidden(D_31,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1693,plain,(
    ! [D_243] :
      ( r2_hidden(D_243,'#skF_21')
      | ~ r2_hidden(D_243,'#skF_20') ) ),
    inference(resolution,[status(thm)],[c_1678,c_44])).

tff(c_3706,plain,(
    ! [B_355] :
      ( r2_hidden('#skF_2'('#skF_20',B_355),'#skF_21')
      | r1_tarski('#skF_20',B_355) ) ),
    inference(resolution,[status(thm)],[c_3461,c_1693])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden('#skF_2'(A_15,B_16),B_16)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3710,plain,(
    r1_tarski('#skF_20','#skF_21') ),
    inference(resolution,[status(thm)],[c_3706,c_20])).

tff(c_3722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_222,c_3710])).
%------------------------------------------------------------------------------
