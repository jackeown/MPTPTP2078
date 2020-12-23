%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0024+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:10 EST 2020

% Result     : Theorem 23.12s
% Output     : CNFRefutation 23.12s
% Verified   : 
% Statistics : Number of formulae       :   55 (  58 expanded)
%              Number of leaves         :   41 (  43 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  34 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

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

tff(f_127,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

tff(f_291,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

tff(f_294,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_106,plain,(
    ! [A_46] : k3_xboole_0(A_46,A_46) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2553,plain,(
    ! [A_324,B_325,C_326] : k3_xboole_0(k3_xboole_0(A_324,B_325),C_326) = k3_xboole_0(A_324,k3_xboole_0(B_325,C_326)) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_15034,plain,(
    ! [C_742,A_743,B_744] : k3_xboole_0(C_742,k3_xboole_0(A_743,B_744)) = k3_xboole_0(A_743,k3_xboole_0(B_744,C_742)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2553,c_8])).

tff(c_15520,plain,(
    ! [A_46,A_743] : k3_xboole_0(A_46,k3_xboole_0(A_743,A_46)) = k3_xboole_0(A_743,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_15034])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_2'(A_15,B_16),A_15)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1571,plain,(
    ! [D_268,A_269,B_270] :
      ( r2_hidden(D_268,A_269)
      | ~ r2_hidden(D_268,k3_xboole_0(A_269,B_270)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_76524,plain,(
    ! [A_1604,B_1605,B_1606] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_1604,B_1605),B_1606),A_1604)
      | r1_tarski(k3_xboole_0(A_1604,B_1605),B_1606) ) ),
    inference(resolution,[status(thm)],[c_22,c_1571])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden('#skF_2'(A_15,B_16),B_16)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_76773,plain,(
    ! [A_1607,B_1608] : r1_tarski(k3_xboole_0(A_1607,B_1608),A_1607) ),
    inference(resolution,[status(thm)],[c_76524,c_20])).

tff(c_76909,plain,(
    ! [A_743,A_46] : r1_tarski(k3_xboole_0(A_743,A_46),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_15520,c_76773])).

tff(c_220,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_20','#skF_21'),'#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_253,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_21','#skF_20'),'#skF_20') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_220])).

tff(c_77020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76909,c_253])).
%------------------------------------------------------------------------------
