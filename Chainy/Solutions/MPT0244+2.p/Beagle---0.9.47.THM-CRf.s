%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0244+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:21 EST 2020

% Result     : Theorem 15.52s
% Output     : CNFRefutation 15.52s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 358 expanded)
%              Number of leaves         :   91 ( 164 expanded)
%              Depth                    :   13
%              Number of atoms          :  161 ( 484 expanded)
%              Number of equality atoms :   75 ( 250 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_26 > #skF_11 > #skF_41 > #skF_33 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_32 > #skF_43 > #skF_31 > #skF_4 > #skF_36 > #skF_10 > #skF_37 > #skF_12 > #skF_45 > #skF_28 > #skF_46 > #skF_35 > #skF_5 > #skF_19 > #skF_30 > #skF_27 > #skF_9 > #skF_7 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_3 > #skF_38 > #skF_2 > #skF_21 > #skF_40 > #skF_44 > #skF_8 > #skF_25 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_42 > #skF_39

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

tff('#skF_43',type,(
    '#skF_43': $i )).

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

tff('#skF_44',type,(
    '#skF_44': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

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

tff(f_265,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_479,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

tff(f_1395,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_1382,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_1199,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_473,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_453,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t22_xboole_1)).

tff(f_1295,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_679,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t70_xboole_1)).

tff(f_1204,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_354,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t10_xboole_1)).

tff(f_1399,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_196,plain,(
    ! [B_82] : r1_tarski(B_82,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1235,plain,(
    ! [A_1117] :
      ( k1_xboole_0 = A_1117
      | ~ v1_xboole_0(A_1117) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1244,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1235])).

tff(c_326,plain,(
    ! [A_217] : r1_tarski(k1_xboole_0,A_217) ),
    inference(cnfTransformation,[status(thm)],[f_479])).

tff(c_1250,plain,(
    ! [A_217] : r1_tarski('#skF_9',A_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_326])).

tff(c_1100,plain,
    ( ~ r1_tarski('#skF_43',k1_tarski('#skF_44'))
    | k1_xboole_0 != '#skF_45' ),
    inference(cnfTransformation,[status(thm)],[f_1395])).

tff(c_1161,plain,(
    k1_xboole_0 != '#skF_45' ),
    inference(splitLeft,[status(thm)],[c_1100])).

tff(c_1253,plain,(
    '#skF_45' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1161])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_9629,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_190])).

tff(c_1088,plain,(
    ! [A_1086,B_1087] :
      ( r1_tarski(k1_tarski(A_1086),B_1087)
      | ~ r2_hidden(A_1086,B_1087) ) ),
    inference(cnfTransformation,[status(thm)],[f_1382])).

tff(c_1096,plain,
    ( ~ r1_tarski('#skF_43',k1_tarski('#skF_44'))
    | k1_tarski('#skF_46') != '#skF_45' ),
    inference(cnfTransformation,[status(thm)],[f_1395])).

tff(c_1266,plain,(
    k1_tarski('#skF_46') != '#skF_45' ),
    inference(splitLeft,[status(thm)],[c_1096])).

tff(c_7090,plain,(
    ! [A_1419,B_1420] :
      ( k2_xboole_0(k1_tarski(A_1419),B_1420) = B_1420
      | ~ r2_hidden(A_1419,B_1420) ) ),
    inference(cnfTransformation,[status(thm)],[f_1199])).

tff(c_1106,plain,
    ( k1_tarski('#skF_44') = '#skF_43'
    | k1_xboole_0 = '#skF_43'
    | r1_tarski('#skF_45',k1_tarski('#skF_46')) ),
    inference(cnfTransformation,[status(thm)],[f_1395])).

tff(c_1501,plain,
    ( k1_tarski('#skF_44') = '#skF_43'
    | '#skF_43' = '#skF_9'
    | r1_tarski('#skF_45',k1_tarski('#skF_46')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1106])).

tff(c_1502,plain,(
    r1_tarski('#skF_45',k1_tarski('#skF_46')) ),
    inference(splitLeft,[status(thm)],[c_1501])).

tff(c_3759,plain,(
    ! [A_1310,B_1311] :
      ( k3_xboole_0(A_1310,B_1311) = A_1310
      | ~ r1_tarski(A_1310,B_1311) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_3815,plain,(
    k3_xboole_0('#skF_45',k1_tarski('#skF_46')) = '#skF_45' ),
    inference(resolution,[status(thm)],[c_1502,c_3759])).

tff(c_1974,plain,(
    ! [B_1188,A_1189] : k3_xboole_0(B_1188,A_1189) = k3_xboole_0(A_1189,B_1188) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_308,plain,(
    ! [A_193,B_194] : k2_xboole_0(A_193,k3_xboole_0(A_193,B_194)) = A_193 ),
    inference(cnfTransformation,[status(thm)],[f_453])).

tff(c_1989,plain,(
    ! [A_1189,B_1188] : k2_xboole_0(A_1189,k3_xboole_0(B_1188,A_1189)) = A_1189 ),
    inference(superposition,[status(thm),theory(equality)],[c_1974,c_308])).

tff(c_3848,plain,(
    k2_xboole_0(k1_tarski('#skF_46'),'#skF_45') = k1_tarski('#skF_46') ),
    inference(superposition,[status(thm),theory(equality)],[c_3815,c_1989])).

tff(c_7100,plain,
    ( k1_tarski('#skF_46') = '#skF_45'
    | ~ r2_hidden('#skF_46','#skF_45') ),
    inference(superposition,[status(thm),theory(equality)],[c_7090,c_3848])).

tff(c_7211,plain,(
    ~ r2_hidden('#skF_46','#skF_45') ),
    inference(negUnitSimplification,[status(thm)],[c_1266,c_7100])).

tff(c_1591,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_190])).

tff(c_1032,plain,(
    ! [A_1038,B_1039] :
      ( r1_xboole_0(k1_tarski(A_1038),k1_tarski(B_1039))
      | B_1039 = A_1038 ) ),
    inference(cnfTransformation,[status(thm)],[f_1295])).

tff(c_9105,plain,(
    ! [A_1475,C_1476,B_1477] :
      ( r1_xboole_0(A_1475,C_1476)
      | ~ r1_xboole_0(A_1475,k2_xboole_0(B_1477,C_1476)) ) ),
    inference(cnfTransformation,[status(thm)],[f_679])).

tff(c_9256,plain,(
    ! [A_1479] :
      ( r1_xboole_0(A_1479,'#skF_45')
      | ~ r1_xboole_0(A_1479,k1_tarski('#skF_46')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3848,c_9105])).

tff(c_9312,plain,(
    ! [A_1480] :
      ( r1_xboole_0(k1_tarski(A_1480),'#skF_45')
      | A_1480 = '#skF_46' ) ),
    inference(resolution,[status(thm)],[c_1032,c_9256])).

tff(c_972,plain,(
    ! [A_998,B_999] :
      ( ~ r2_hidden(A_998,B_999)
      | ~ r1_xboole_0(k1_tarski(A_998),B_999) ) ),
    inference(cnfTransformation,[status(thm)],[f_1204])).

tff(c_9329,plain,(
    ! [A_1481] :
      ( ~ r2_hidden(A_1481,'#skF_45')
      | A_1481 = '#skF_46' ) ),
    inference(resolution,[status(thm)],[c_9312,c_972])).

tff(c_9341,plain,
    ( '#skF_18'('#skF_45') = '#skF_46'
    | '#skF_45' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1591,c_9329])).

tff(c_9346,plain,(
    '#skF_18'('#skF_45') = '#skF_46' ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_9341])).

tff(c_9353,plain,
    ( r2_hidden('#skF_46','#skF_45')
    | '#skF_45' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_9346,c_1591])).

tff(c_9358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_7211,c_9353])).

tff(c_9359,plain,
    ( '#skF_43' = '#skF_9'
    | k1_tarski('#skF_44') = '#skF_43' ),
    inference(splitRight,[status(thm)],[c_1501])).

tff(c_9396,plain,(
    k1_tarski('#skF_44') = '#skF_43' ),
    inference(splitLeft,[status(thm)],[c_9359])).

tff(c_1104,plain,
    ( ~ r1_tarski('#skF_43',k1_tarski('#skF_44'))
    | r1_tarski('#skF_45',k1_tarski('#skF_46')) ),
    inference(cnfTransformation,[status(thm)],[f_1395])).

tff(c_1316,plain,(
    ~ r1_tarski('#skF_43',k1_tarski('#skF_44')) ),
    inference(splitLeft,[status(thm)],[c_1104])).

tff(c_9397,plain,(
    ~ r1_tarski('#skF_43','#skF_43') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9396,c_1316])).

tff(c_9400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_9397])).

tff(c_9401,plain,(
    '#skF_43' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_9359])).

tff(c_9403,plain,(
    ~ r1_tarski('#skF_9',k1_tarski('#skF_44')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9401,c_1316])).

tff(c_9406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_9403])).

tff(c_9407,plain,(
    r1_tarski('#skF_45',k1_tarski('#skF_46')) ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_11959,plain,(
    ! [A_1662,B_1663] :
      ( k3_xboole_0(A_1662,B_1663) = A_1662
      | ~ r1_tarski(A_1662,B_1663) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_12011,plain,(
    k3_xboole_0('#skF_45',k1_tarski('#skF_46')) = '#skF_45' ),
    inference(resolution,[status(thm)],[c_9407,c_11959])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10284,plain,(
    ! [A_1578,B_1579] : k2_xboole_0(A_1578,k3_xboole_0(A_1578,B_1579)) = A_1578 ),
    inference(cnfTransformation,[status(thm)],[f_453])).

tff(c_10321,plain,(
    ! [B_8,A_7] : k2_xboole_0(B_8,k3_xboole_0(A_7,B_8)) = B_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_10284])).

tff(c_12197,plain,(
    k2_xboole_0(k1_tarski('#skF_46'),'#skF_45') = k1_tarski('#skF_46') ),
    inference(superposition,[status(thm),theory(equality)],[c_12011,c_10321])).

tff(c_17087,plain,(
    ! [A_1825,C_1826,B_1827] :
      ( r1_tarski(A_1825,k2_xboole_0(C_1826,B_1827))
      | ~ r1_tarski(A_1825,B_1827) ) ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_17186,plain,(
    ! [A_1830] :
      ( r1_tarski(A_1830,k1_tarski('#skF_46'))
      | ~ r1_tarski(A_1830,'#skF_45') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12197,c_17087])).

tff(c_1108,plain,(
    ! [B_1092,A_1091] :
      ( B_1092 = A_1091
      | ~ r1_tarski(k1_tarski(A_1091),k1_tarski(B_1092)) ) ),
    inference(cnfTransformation,[status(thm)],[f_1399])).

tff(c_17783,plain,(
    ! [A_1842] :
      ( A_1842 = '#skF_46'
      | ~ r1_tarski(k1_tarski(A_1842),'#skF_45') ) ),
    inference(resolution,[status(thm)],[c_17186,c_1108])).

tff(c_17961,plain,(
    ! [A_1845] :
      ( A_1845 = '#skF_46'
      | ~ r2_hidden(A_1845,'#skF_45') ) ),
    inference(resolution,[status(thm)],[c_1088,c_17783])).

tff(c_17973,plain,
    ( '#skF_18'('#skF_45') = '#skF_46'
    | '#skF_45' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9629,c_17961])).

tff(c_17978,plain,(
    '#skF_18'('#skF_45') = '#skF_46' ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_17973])).

tff(c_17985,plain,
    ( r2_hidden('#skF_46','#skF_45')
    | '#skF_45' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_17978,c_9629])).

tff(c_17989,plain,(
    r2_hidden('#skF_46','#skF_45') ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_17985])).

tff(c_25182,plain,(
    ! [B_2020,A_2021] :
      ( B_2020 = A_2021
      | ~ r1_tarski(B_2020,A_2021)
      | ~ r1_tarski(A_2021,B_2020) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_25248,plain,
    ( k1_tarski('#skF_46') = '#skF_45'
    | ~ r1_tarski(k1_tarski('#skF_46'),'#skF_45') ),
    inference(resolution,[status(thm)],[c_9407,c_25182])).

tff(c_25287,plain,(
    ~ r1_tarski(k1_tarski('#skF_46'),'#skF_45') ),
    inference(negUnitSimplification,[status(thm)],[c_1266,c_25248])).

tff(c_25303,plain,(
    ~ r2_hidden('#skF_46','#skF_45') ),
    inference(resolution,[status(thm)],[c_1088,c_25287])).

tff(c_25310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17989,c_25303])).

tff(c_25312,plain,(
    k1_tarski('#skF_46') = '#skF_45' ),
    inference(splitRight,[status(thm)],[c_1096])).

tff(c_1098,plain,
    ( k1_tarski('#skF_44') = '#skF_43'
    | k1_xboole_0 = '#skF_43'
    | k1_tarski('#skF_46') != '#skF_45' ),
    inference(cnfTransformation,[status(thm)],[f_1395])).

tff(c_25326,plain,
    ( k1_tarski('#skF_44') = '#skF_43'
    | '#skF_43' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25312,c_1244,c_1098])).

tff(c_25327,plain,(
    '#skF_43' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_25326])).

tff(c_25311,plain,(
    ~ r1_tarski('#skF_43',k1_tarski('#skF_44')) ),
    inference(splitRight,[status(thm)],[c_1096])).

tff(c_25384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_25327,c_25311])).

tff(c_25385,plain,(
    k1_tarski('#skF_44') = '#skF_43' ),
    inference(splitRight,[status(thm)],[c_25326])).

tff(c_25454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_25385,c_25311])).

tff(c_25456,plain,(
    k1_xboole_0 = '#skF_45' ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_25475,plain,(
    ! [A_217] : r1_tarski('#skF_45',A_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25456,c_326])).

tff(c_1102,plain,
    ( k1_tarski('#skF_44') = '#skF_43'
    | k1_xboole_0 = '#skF_43'
    | k1_xboole_0 != '#skF_45' ),
    inference(cnfTransformation,[status(thm)],[f_1395])).

tff(c_25481,plain,
    ( k1_tarski('#skF_44') = '#skF_43'
    | '#skF_43' = '#skF_45' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25456,c_25456,c_1102])).

tff(c_25482,plain,(
    '#skF_43' = '#skF_45' ),
    inference(splitLeft,[status(thm)],[c_25481])).

tff(c_25455,plain,(
    ~ r1_tarski('#skF_43',k1_tarski('#skF_44')) ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_25483,plain,(
    ~ r1_tarski('#skF_45',k1_tarski('#skF_44')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25482,c_25455])).

tff(c_25486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25475,c_25483])).

tff(c_25487,plain,(
    k1_tarski('#skF_44') = '#skF_43' ),
    inference(splitRight,[status(thm)],[c_25481])).

tff(c_25489,plain,(
    ~ r1_tarski('#skF_43','#skF_43') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25487,c_25455])).

tff(c_25492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_25489])).
%------------------------------------------------------------------------------
