%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0252+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:21 EST 2020

% Result     : Theorem 12.47s
% Output     : CNFRefutation 12.47s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 111 expanded)
%              Number of leaves         :   84 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 (  47 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_26 > #skF_11 > #skF_41 > #skF_33 > #skF_18 > #skF_6 > #skF_44 > #skF_1 > #skF_17 > #skF_32 > #skF_31 > #skF_4 > #skF_36 > #skF_10 > #skF_47 > #skF_37 > #skF_12 > #skF_45 > #skF_28 > #skF_46 > #skF_35 > #skF_5 > #skF_19 > #skF_30 > #skF_27 > #skF_9 > #skF_7 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_3 > #skF_38 > #skF_2 > #skF_21 > #skF_40 > #skF_8 > #skF_25 > #skF_43 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_42 > #skF_39

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_41',type,(
    '#skF_41': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_44',type,(
    '#skF_44': ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_31',type,(
    '#skF_31': ( $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_36',type,(
    '#skF_36': ( $i * ( $i * $i ) ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_47',type,(
    '#skF_47': $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_45',type,(
    '#skF_45': $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_46',type,(
    '#skF_46': $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * $i ) > $i )).

tff('#skF_34',type,(
    '#skF_34': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_38',type,(
    '#skF_38': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_43',type,(
    '#skF_43': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_29',type,(
    '#skF_29': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(f_1492,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_880,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',d2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_451,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t21_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_849,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',commutativity_k2_tarski)).

tff(f_473,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

tff(c_1146,plain,(
    ~ r2_hidden('#skF_45','#skF_47') ),
    inference(cnfTransformation,[status(thm)],[f_1492])).

tff(c_544,plain,(
    ! [D_438,A_433] : r2_hidden(D_438,k2_tarski(A_433,D_438)) ),
    inference(cnfTransformation,[status(thm)],[f_880])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_306,plain,(
    ! [A_191,B_192] : k3_xboole_0(A_191,k2_xboole_0(A_191,B_192)) = A_191 ),
    inference(cnfTransformation,[status(thm)],[f_451])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_504,plain,(
    ! [B_420,A_419] : k2_tarski(B_420,A_419) = k2_tarski(A_419,B_420) ),
    inference(cnfTransformation,[status(thm)],[f_849])).

tff(c_1148,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_45','#skF_46'),'#skF_47'),'#skF_47') ),
    inference(cnfTransformation,[status(thm)],[f_1492])).

tff(c_1174,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_46','#skF_45'),'#skF_47'),'#skF_47') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_1148])).

tff(c_1201,plain,(
    r1_tarski(k2_xboole_0('#skF_47',k2_tarski('#skF_46','#skF_45')),'#skF_47') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1174])).

tff(c_4493,plain,(
    ! [A_1368,B_1369] :
      ( k3_xboole_0(A_1368,B_1369) = A_1368
      | ~ r1_tarski(A_1368,B_1369) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_4553,plain,(
    k3_xboole_0(k2_xboole_0('#skF_47',k2_tarski('#skF_46','#skF_45')),'#skF_47') = k2_xboole_0('#skF_47',k2_tarski('#skF_46','#skF_45')) ),
    inference(resolution,[status(thm)],[c_1201,c_4493])).

tff(c_4661,plain,(
    k3_xboole_0('#skF_47',k2_xboole_0('#skF_47',k2_tarski('#skF_46','#skF_45'))) = k2_xboole_0('#skF_47',k2_tarski('#skF_46','#skF_45')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4553,c_8])).

tff(c_4691,plain,(
    k2_xboole_0('#skF_47',k2_tarski('#skF_46','#skF_45')) = '#skF_47' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_4661])).

tff(c_2194,plain,(
    ! [A_1242,B_1243] : k3_xboole_0(A_1242,k2_xboole_0(A_1242,B_1243)) = A_1242 ),
    inference(cnfTransformation,[status(thm)],[f_451])).

tff(c_2222,plain,(
    ! [B_6,A_5] : k3_xboole_0(B_6,k2_xboole_0(A_5,B_6)) = B_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2194])).

tff(c_4716,plain,(
    k3_xboole_0(k2_tarski('#skF_46','#skF_45'),'#skF_47') = k2_tarski('#skF_46','#skF_45') ),
    inference(superposition,[status(thm),theory(equality)],[c_4691,c_2222])).

tff(c_6320,plain,(
    k3_xboole_0('#skF_47',k2_tarski('#skF_46','#skF_45')) = k2_tarski('#skF_46','#skF_45') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4716])).

tff(c_46,plain,(
    ! [D_31,A_26,B_27] :
      ( r2_hidden(D_31,A_26)
      | ~ r2_hidden(D_31,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9627,plain,(
    ! [D_1524] :
      ( r2_hidden(D_1524,'#skF_47')
      | ~ r2_hidden(D_1524,k2_tarski('#skF_46','#skF_45')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6320,c_46])).

tff(c_9651,plain,(
    r2_hidden('#skF_45','#skF_47') ),
    inference(resolution,[status(thm)],[c_544,c_9627])).

tff(c_9664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1146,c_9651])).
%------------------------------------------------------------------------------
