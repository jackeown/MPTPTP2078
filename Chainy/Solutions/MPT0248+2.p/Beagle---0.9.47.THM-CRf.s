%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0248+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:21 EST 2020

% Result     : Theorem 19.30s
% Output     : CNFRefutation 19.65s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 701 expanded)
%              Number of leaves         :  106 ( 283 expanded)
%              Depth                    :   18
%              Number of atoms          :  247 (1132 expanded)
%              Number of equality atoms :  118 ( 754 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_1468,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_430,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t1_boole)).

tff(f_588,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t5_boole)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_1232,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_523,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t40_xboole_1)).

tff(f_1209,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_451,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t21_xboole_1)).

tff(f_199,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

tff(f_816,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t98_xboole_1)).

tff(f_185,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

tff(f_736,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t7_boole)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

tff(f_871,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',d1_tarski)).

tff(f_1402,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_539,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t45_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_453,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t22_xboole_1)).

tff(f_738,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t7_xboole_1)).

tff(f_541,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t46_xboole_1)).

tff(f_489,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t32_xboole_1)).

tff(f_679,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t70_xboole_1)).

tff(f_631,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t66_xboole_1)).

tff(f_509,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t37_xboole_1)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1233,plain,(
    ! [A_1129] :
      ( k1_xboole_0 = A_1129
      | ~ v1_xboole_0(A_1129) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1242,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1233])).

tff(c_1126,plain,
    ( k1_tarski('#skF_45') != '#skF_47'
    | k1_xboole_0 != '#skF_46' ),
    inference(cnfTransformation,[status(thm)],[f_1468])).

tff(c_1232,plain,(
    k1_xboole_0 != '#skF_46' ),
    inference(splitLeft,[status(thm)],[c_1126])).

tff(c_1244,plain,(
    '#skF_46' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1232])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_1666,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_190])).

tff(c_1124,plain,
    ( k1_xboole_0 != '#skF_47'
    | k1_tarski('#skF_45') != '#skF_46' ),
    inference(cnfTransformation,[status(thm)],[f_1468])).

tff(c_1276,plain,
    ( '#skF_47' != '#skF_9'
    | k1_tarski('#skF_45') != '#skF_46' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1124])).

tff(c_1277,plain,(
    k1_tarski('#skF_45') != '#skF_46' ),
    inference(splitLeft,[status(thm)],[c_1276])).

tff(c_296,plain,(
    ! [A_183] : k2_xboole_0(A_183,k1_xboole_0) = A_183 ),
    inference(cnfTransformation,[status(thm)],[f_430])).

tff(c_1309,plain,(
    ! [A_183] : k2_xboole_0(A_183,'#skF_9') = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_296])).

tff(c_1130,plain,(
    k2_xboole_0('#skF_46','#skF_47') = k1_tarski('#skF_45') ),
    inference(cnfTransformation,[status(thm)],[f_1468])).

tff(c_398,plain,(
    ! [A_302] : k5_xboole_0(A_302,k1_xboole_0) = A_302 ),
    inference(cnfTransformation,[status(thm)],[f_588])).

tff(c_1279,plain,(
    ! [A_302] : k5_xboole_0(A_302,'#skF_9') = A_302 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_398])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_988,plain,(
    ! [A_1011,B_1012] :
      ( k4_xboole_0(k1_tarski(A_1011),B_1012) = k1_xboole_0
      | ~ r2_hidden(A_1011,B_1012) ) ),
    inference(cnfTransformation,[status(thm)],[f_1232])).

tff(c_11859,plain,(
    ! [A_1011,B_1012] :
      ( k4_xboole_0(k1_tarski(A_1011),B_1012) = '#skF_9'
      | ~ r2_hidden(A_1011,B_1012) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_988])).

tff(c_13819,plain,(
    ! [A_1571,B_1572] : k4_xboole_0(k2_xboole_0(A_1571,B_1572),B_1572) = k4_xboole_0(A_1571,B_1572) ),
    inference(cnfTransformation,[status(thm)],[f_523])).

tff(c_13973,plain,(
    k4_xboole_0(k1_tarski('#skF_45'),'#skF_47') = k4_xboole_0('#skF_46','#skF_47') ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_13819])).

tff(c_14415,plain,
    ( k4_xboole_0('#skF_46','#skF_47') = '#skF_9'
    | ~ r2_hidden('#skF_45','#skF_47') ),
    inference(superposition,[status(thm),theory(equality)],[c_11859,c_13973])).

tff(c_14785,plain,(
    ~ r2_hidden('#skF_45','#skF_47') ),
    inference(splitLeft,[status(thm)],[c_14415])).

tff(c_2522,plain,(
    ! [A_1247,B_1248] :
      ( r1_xboole_0(k1_tarski(A_1247),B_1248)
      | r2_hidden(A_1247,B_1248) ) ),
    inference(cnfTransformation,[status(thm)],[f_1209])).

tff(c_116,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(B_52,A_51)
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_17376,plain,(
    ! [B_1639,A_1640] :
      ( r1_xboole_0(B_1639,k1_tarski(A_1640))
      | r2_hidden(A_1640,B_1639) ) ),
    inference(resolution,[status(thm)],[c_2522,c_116])).

tff(c_2057,plain,(
    ! [B_1217,A_1218] : k2_xboole_0(B_1217,A_1218) = k2_xboole_0(A_1218,B_1217) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_306,plain,(
    ! [A_191,B_192] : k3_xboole_0(A_191,k2_xboole_0(A_191,B_192)) = A_191 ),
    inference(cnfTransformation,[status(thm)],[f_451])).

tff(c_2439,plain,(
    ! [A_1245,B_1246] : k3_xboole_0(A_1245,k2_xboole_0(B_1246,A_1245)) = A_1245 ),
    inference(superposition,[status(thm),theory(equality)],[c_2057,c_306])).

tff(c_2491,plain,(
    k3_xboole_0('#skF_47',k1_tarski('#skF_45')) = '#skF_47' ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_2439])).

tff(c_7432,plain,(
    ! [A_1443,B_1444,C_1445] :
      ( ~ r1_xboole_0(A_1443,B_1444)
      | ~ r2_hidden(C_1445,k3_xboole_0(A_1443,B_1444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_7450,plain,(
    ! [C_1445] :
      ( ~ r1_xboole_0('#skF_47',k1_tarski('#skF_45'))
      | ~ r2_hidden(C_1445,'#skF_47') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2491,c_7432])).

tff(c_7803,plain,(
    ~ r1_xboole_0('#skF_47',k1_tarski('#skF_45')) ),
    inference(splitLeft,[status(thm)],[c_7450])).

tff(c_17383,plain,(
    r2_hidden('#skF_45','#skF_47') ),
    inference(resolution,[status(thm)],[c_17376,c_7803])).

tff(c_17418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14785,c_17383])).

tff(c_17419,plain,(
    k4_xboole_0('#skF_46','#skF_47') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_14415])).

tff(c_498,plain,(
    ! [A_411,B_412] : k5_xboole_0(A_411,k4_xboole_0(B_412,A_411)) = k2_xboole_0(A_411,B_412) ),
    inference(cnfTransformation,[status(thm)],[f_816])).

tff(c_17479,plain,(
    k5_xboole_0('#skF_47','#skF_9') = k2_xboole_0('#skF_47','#skF_46') ),
    inference(superposition,[status(thm),theory(equality)],[c_17419,c_498])).

tff(c_17555,plain,(
    k1_tarski('#skF_45') = '#skF_47' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1279,c_6,c_17479])).

tff(c_17617,plain,(
    '#skF_47' != '#skF_46' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17555,c_1277])).

tff(c_22914,plain,(
    ! [A_1728,B_1729] :
      ( r2_hidden('#skF_15'(A_1728,B_1729),B_1729)
      | r1_xboole_0(A_1728,B_1729) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_452,plain,(
    ! [B_360,A_359] :
      ( ~ v1_xboole_0(B_360)
      | ~ r2_hidden(A_359,B_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_736])).

tff(c_22981,plain,(
    ! [B_1730,A_1731] :
      ( ~ v1_xboole_0(B_1730)
      | r1_xboole_0(A_1731,B_1730) ) ),
    inference(resolution,[status(thm)],[c_22914,c_452])).

tff(c_23029,plain,(
    ! [B_1732,A_1733] :
      ( r1_xboole_0(B_1732,A_1733)
      | ~ v1_xboole_0(B_1732) ) ),
    inference(resolution,[status(thm)],[c_22981,c_116])).

tff(c_1982,plain,(
    ! [A_1213,B_1214] : k3_xboole_0(A_1213,k2_xboole_0(A_1213,B_1214)) = A_1213 ),
    inference(cnfTransformation,[status(thm)],[f_451])).

tff(c_2017,plain,(
    k3_xboole_0('#skF_46',k1_tarski('#skF_45')) = '#skF_46' ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_1982])).

tff(c_7456,plain,(
    ! [C_1445] :
      ( ~ r1_xboole_0('#skF_46',k1_tarski('#skF_45'))
      | ~ r2_hidden(C_1445,'#skF_46') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2017,c_7432])).

tff(c_7518,plain,(
    ~ r1_xboole_0('#skF_46',k1_tarski('#skF_45')) ),
    inference(splitLeft,[status(thm)],[c_7456])).

tff(c_17593,plain,(
    ~ r1_xboole_0('#skF_46','#skF_47') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17555,c_7518])).

tff(c_23067,plain,(
    ~ v1_xboole_0('#skF_46') ),
    inference(resolution,[status(thm)],[c_23029,c_17593])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | r2_hidden('#skF_1'(A_11),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_17615,plain,(
    k3_xboole_0('#skF_46','#skF_47') = '#skF_46' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17555,c_2017])).

tff(c_19890,plain,(
    ! [D_1683,B_1684,A_1685] :
      ( r2_hidden(D_1683,B_1684)
      | ~ r2_hidden(D_1683,k3_xboole_0(A_1685,B_1684)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24033,plain,(
    ! [D_1756] :
      ( r2_hidden(D_1756,'#skF_47')
      | ~ r2_hidden(D_1756,'#skF_46') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17615,c_19890])).

tff(c_530,plain,(
    ! [C_432,A_428] :
      ( C_432 = A_428
      | ~ r2_hidden(C_432,k1_tarski(A_428)) ) ),
    inference(cnfTransformation,[status(thm)],[f_871])).

tff(c_17753,plain,(
    ! [C_432] :
      ( C_432 = '#skF_45'
      | ~ r2_hidden(C_432,'#skF_47') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17555,c_530])).

tff(c_24149,plain,(
    ! [D_1757] :
      ( D_1757 = '#skF_45'
      | ~ r2_hidden(D_1757,'#skF_46') ) ),
    inference(resolution,[status(thm)],[c_24033,c_17753])).

tff(c_24169,plain,
    ( '#skF_1'('#skF_46') = '#skF_45'
    | v1_xboole_0('#skF_46') ),
    inference(resolution,[status(thm)],[c_14,c_24149])).

tff(c_24181,plain,(
    '#skF_1'('#skF_46') = '#skF_45' ),
    inference(negUnitSimplification,[status(thm)],[c_23067,c_24169])).

tff(c_24191,plain,
    ( v1_xboole_0('#skF_46')
    | r2_hidden('#skF_45','#skF_46') ),
    inference(superposition,[status(thm),theory(equality)],[c_24181,c_14])).

tff(c_24195,plain,(
    r2_hidden('#skF_45','#skF_46') ),
    inference(negUnitSimplification,[status(thm)],[c_23067,c_24191])).

tff(c_1094,plain,(
    ! [A_1092,B_1093] :
      ( r1_tarski(k1_tarski(A_1092),B_1093)
      | ~ r2_hidden(A_1092,B_1093) ) ),
    inference(cnfTransformation,[status(thm)],[f_1402])).

tff(c_26412,plain,(
    ! [B_1787] :
      ( r1_tarski('#skF_47',B_1787)
      | ~ r2_hidden('#skF_45',B_1787) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17555,c_1094])).

tff(c_26477,plain,(
    r1_tarski('#skF_47','#skF_46') ),
    inference(resolution,[status(thm)],[c_24195,c_26412])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_364,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_1161,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,B_261) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_26525,plain,(
    k2_xboole_0('#skF_47','#skF_46') = '#skF_46' ),
    inference(resolution,[status(thm)],[c_26477,c_1161])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1927,plain,(
    ! [A_1199,B_1200] : k2_xboole_0(A_1199,k3_xboole_0(A_1199,B_1200)) = A_1199 ),
    inference(cnfTransformation,[status(thm)],[f_453])).

tff(c_2542,plain,(
    ! [A_1252,B_1253] : k2_xboole_0(A_1252,k3_xboole_0(B_1253,A_1252)) = A_1252 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1927])).

tff(c_2593,plain,(
    k2_xboole_0(k1_tarski('#skF_45'),'#skF_46') = k1_tarski('#skF_45') ),
    inference(superposition,[status(thm),theory(equality)],[c_2017,c_2542])).

tff(c_17611,plain,(
    k2_xboole_0('#skF_47','#skF_46') = '#skF_47' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17555,c_17555,c_2593])).

tff(c_26528,plain,(
    '#skF_47' = '#skF_46' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26525,c_17611])).

tff(c_26530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17617,c_26528])).

tff(c_26533,plain,(
    ! [C_1788] : ~ r2_hidden(C_1788,'#skF_47') ),
    inference(splitRight,[status(thm)],[c_7450])).

tff(c_26543,plain,(
    '#skF_47' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1666,c_26533])).

tff(c_26571,plain,(
    k2_xboole_0('#skF_46','#skF_9') = k1_tarski('#skF_45') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26543,c_1130])).

tff(c_26582,plain,(
    k1_tarski('#skF_45') = '#skF_46' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_26571])).

tff(c_26584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1277,c_26582])).

tff(c_26587,plain,(
    ! [C_1789] : ~ r2_hidden(C_1789,'#skF_46') ),
    inference(splitRight,[status(thm)],[c_7456])).

tff(c_26595,plain,(
    '#skF_46' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1666,c_26587])).

tff(c_26600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1244,c_26595])).

tff(c_26602,plain,(
    k1_tarski('#skF_45') = '#skF_46' ),
    inference(splitRight,[status(thm)],[c_1276])).

tff(c_1128,plain,
    ( k1_tarski('#skF_45') != '#skF_47'
    | k1_tarski('#skF_45') != '#skF_46' ),
    inference(cnfTransformation,[status(thm)],[f_1468])).

tff(c_26626,plain,(
    '#skF_47' != '#skF_46' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26602,c_26602,c_1128])).

tff(c_26612,plain,(
    k2_xboole_0('#skF_46','#skF_47') = '#skF_46' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26602,c_1130])).

tff(c_27377,plain,(
    ! [B_1872,A_1873] : k2_xboole_0(B_1872,A_1873) = k2_xboole_0(A_1873,B_1872) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_454,plain,(
    ! [A_361,B_362] : r1_tarski(A_361,k2_xboole_0(A_361,B_362)) ),
    inference(cnfTransformation,[status(thm)],[f_738])).

tff(c_27525,plain,(
    ! [A_1877,B_1878] : r1_tarski(A_1877,k2_xboole_0(B_1878,A_1877)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27377,c_454])).

tff(c_27537,plain,(
    r1_tarski('#skF_47','#skF_46') ),
    inference(superposition,[status(thm),theory(equality)],[c_26612,c_27525])).

tff(c_28522,plain,(
    ! [A_1945,B_1946] :
      ( k2_xboole_0(A_1945,B_1946) = B_1946
      | ~ r1_tarski(A_1945,B_1946) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_28568,plain,(
    k2_xboole_0('#skF_47','#skF_46') = '#skF_46' ),
    inference(resolution,[status(thm)],[c_27537,c_28522])).

tff(c_366,plain,(
    ! [A_262,B_263] : k4_xboole_0(A_262,k2_xboole_0(A_262,B_263)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_541])).

tff(c_27765,plain,(
    ! [A_262,B_263] : k4_xboole_0(A_262,k2_xboole_0(A_262,B_263)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_366])).

tff(c_28587,plain,(
    k4_xboole_0('#skF_47','#skF_46') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_28568,c_27765])).

tff(c_40000,plain,(
    ! [B_2218,A_2219] :
      ( B_2218 = A_2219
      | k4_xboole_0(B_2218,A_2219) != k4_xboole_0(A_2219,B_2218) ) ),
    inference(cnfTransformation,[status(thm)],[f_489])).

tff(c_40069,plain,
    ( '#skF_47' = '#skF_46'
    | k4_xboole_0('#skF_46','#skF_47') != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_28587,c_40000])).

tff(c_40087,plain,(
    k4_xboole_0('#skF_46','#skF_47') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_26626,c_40069])).

tff(c_27865,plain,(
    ! [A_1905,B_1906] :
      ( r1_xboole_0(k1_tarski(A_1905),B_1906)
      | r2_hidden(A_1905,B_1906) ) ),
    inference(cnfTransformation,[status(thm)],[f_1209])).

tff(c_27878,plain,(
    ! [B_1906] :
      ( r1_xboole_0('#skF_46',B_1906)
      | r2_hidden('#skF_45',B_1906) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26602,c_27865])).

tff(c_29557,plain,(
    ! [A_1967,B_1968] :
      ( r1_tarski(k1_tarski(A_1967),B_1968)
      | ~ r2_hidden(A_1967,B_1968) ) ),
    inference(cnfTransformation,[status(thm)],[f_1402])).

tff(c_29796,plain,(
    ! [B_1974] :
      ( r1_tarski('#skF_46',B_1974)
      | ~ r2_hidden('#skF_45',B_1974) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26602,c_29557])).

tff(c_31057,plain,(
    ! [B_2027] :
      ( r1_tarski('#skF_46',B_2027)
      | r1_xboole_0('#skF_46',B_2027) ) ),
    inference(resolution,[status(thm)],[c_27878,c_29796])).

tff(c_31085,plain,(
    ! [B_2027] :
      ( r1_xboole_0(B_2027,'#skF_46')
      | r1_tarski('#skF_46',B_2027) ) ),
    inference(resolution,[status(thm)],[c_31057,c_116])).

tff(c_26601,plain,(
    '#skF_47' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1276])).

tff(c_39063,plain,(
    ! [A_2188,B_2189,C_2190] :
      ( r1_xboole_0(A_2188,B_2189)
      | ~ r1_xboole_0(A_2188,k2_xboole_0(B_2189,C_2190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_679])).

tff(c_40098,plain,(
    ! [A_2220] :
      ( r1_xboole_0(A_2220,'#skF_47')
      | ~ r1_xboole_0(A_2220,'#skF_46') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28568,c_39063])).

tff(c_416,plain,(
    ! [A_318] :
      ( ~ r1_xboole_0(A_318,A_318)
      | k1_xboole_0 = A_318 ) ),
    inference(cnfTransformation,[status(thm)],[f_631])).

tff(c_26732,plain,(
    ! [A_318] :
      ( ~ r1_xboole_0(A_318,A_318)
      | A_318 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_416])).

tff(c_40122,plain,
    ( '#skF_47' = '#skF_9'
    | ~ r1_xboole_0('#skF_47','#skF_46') ),
    inference(resolution,[status(thm)],[c_40098,c_26732])).

tff(c_40131,plain,(
    ~ r1_xboole_0('#skF_47','#skF_46') ),
    inference(negUnitSimplification,[status(thm)],[c_26601,c_40122])).

tff(c_40157,plain,(
    r1_tarski('#skF_46','#skF_47') ),
    inference(resolution,[status(thm)],[c_31085,c_40131])).

tff(c_344,plain,(
    ! [A_238,B_239] :
      ( k4_xboole_0(A_238,B_239) = k1_xboole_0
      | ~ r1_tarski(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_509])).

tff(c_33475,plain,(
    ! [A_238,B_239] :
      ( k4_xboole_0(A_238,B_239) = '#skF_9'
      | ~ r1_tarski(A_238,B_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_344])).

tff(c_40171,plain,(
    k4_xboole_0('#skF_46','#skF_47') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40157,c_33475])).

tff(c_40185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40087,c_40171])).

tff(c_40186,plain,(
    k1_tarski('#skF_45') != '#skF_47' ),
    inference(splitRight,[status(thm)],[c_1126])).

tff(c_40759,plain,(
    ! [B_2290,A_2291] : k2_xboole_0(B_2290,A_2291) = k2_xboole_0(A_2291,B_2290) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40187,plain,(
    k1_xboole_0 = '#skF_46' ),
    inference(splitRight,[status(thm)],[c_1126])).

tff(c_424,plain,(
    ! [A_327] :
      ( k1_xboole_0 = A_327
      | ~ v1_xboole_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_40242,plain,(
    ! [A_2227] :
      ( A_2227 = '#skF_46'
      | ~ v1_xboole_0(A_2227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40187,c_424])).

tff(c_40251,plain,(
    '#skF_46' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_40242])).

tff(c_40263,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40251,c_40187])).

tff(c_40313,plain,(
    ! [A_183] : k2_xboole_0(A_183,'#skF_9') = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40263,c_296])).

tff(c_40787,plain,(
    ! [A_2291] : k2_xboole_0('#skF_9',A_2291) = A_2291 ),
    inference(superposition,[status(thm),theory(equality)],[c_40759,c_40313])).

tff(c_40264,plain,(
    k2_xboole_0('#skF_9','#skF_47') = k1_tarski('#skF_45') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40251,c_1130])).

tff(c_40818,plain,(
    k1_tarski('#skF_45') = '#skF_47' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40787,c_40264])).

tff(c_40820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40186,c_40818])).
%------------------------------------------------------------------------------
