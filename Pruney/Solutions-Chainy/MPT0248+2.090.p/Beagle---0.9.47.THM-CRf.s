%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:16 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 600 expanded)
%              Number of leaves         :   40 ( 211 expanded)
%              Depth                    :   21
%              Number of atoms          :  177 (1092 expanded)
%              Number of equality atoms :   95 ( 771 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_95,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_89,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_114,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_84,plain,
    ( k1_xboole_0 != '#skF_10'
    | k1_tarski('#skF_8') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_112,plain,(
    k1_tarski('#skF_8') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_86,plain,
    ( k1_tarski('#skF_8') != '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_113,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_36,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_5'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [A_35] : k5_xboole_0(A_35,k1_xboole_0) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_506,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = k4_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_524,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = k4_xboole_0(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_506])).

tff(c_530,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_524])).

tff(c_42,plain,(
    ! [B_22] : r1_tarski(B_22,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_171,plain,(
    ! [A_68,B_69] :
      ( k2_xboole_0(A_68,B_69) = B_69
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_180,plain,(
    ! [B_70] : k2_xboole_0(B_70,B_70) = B_70 ),
    inference(resolution,[status(thm)],[c_42,c_171])).

tff(c_52,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k2_xboole_0(A_31,B_32)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_186,plain,(
    ! [B_70] : k4_xboole_0(B_70,B_70) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_52])).

tff(c_332,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k4_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_350,plain,(
    ! [B_70] : k4_xboole_0(B_70,k1_xboole_0) = k3_xboole_0(B_70,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_332])).

tff(c_532,plain,(
    ! [B_70] : k3_xboole_0(B_70,B_70) = B_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_350])).

tff(c_90,plain,(
    k2_xboole_0('#skF_9','#skF_10') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_128,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k2_xboole_0(A_58,B_59)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_135,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_128])).

tff(c_353,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k4_xboole_0('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_332])).

tff(c_422,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k3_xboole_0('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_353])).

tff(c_564,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_422])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_663,plain,(
    ! [D_113] :
      ( r2_hidden(D_113,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_113,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_10])).

tff(c_58,plain,(
    ! [C_40,A_36] :
      ( C_40 = A_36
      | ~ r2_hidden(C_40,k1_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_673,plain,(
    ! [D_114] :
      ( D_114 = '#skF_8'
      | ~ r2_hidden(D_114,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_663,c_58])).

tff(c_689,plain,
    ( '#skF_5'('#skF_9') = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_36,c_673])).

tff(c_695,plain,(
    '#skF_5'('#skF_9') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_689])).

tff(c_699,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_36])).

tff(c_702,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_699])).

tff(c_619,plain,(
    ! [D_11] :
      ( r2_hidden(D_11,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_11,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_10])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_690,plain,(
    ! [B_2] :
      ( '#skF_1'('#skF_9',B_2) = '#skF_8'
      | r1_tarski('#skF_9',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_673])).

tff(c_1029,plain,(
    ! [B_137,A_138] :
      ( k1_tarski(B_137) = A_138
      | k1_xboole_0 = A_138
      | ~ r1_tarski(A_138,k1_tarski(B_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1037,plain,(
    ! [B_137] :
      ( k1_tarski(B_137) = '#skF_9'
      | k1_xboole_0 = '#skF_9'
      | '#skF_1'('#skF_9',k1_tarski(B_137)) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_690,c_1029])).

tff(c_2010,plain,(
    ! [B_2350] :
      ( k1_tarski(B_2350) = '#skF_9'
      | '#skF_1'('#skF_9',k1_tarski(B_2350)) = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_1037])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6714,plain,(
    ! [B_18439] :
      ( ~ r2_hidden('#skF_8',k1_tarski(B_18439))
      | r1_tarski('#skF_9',k1_tarski(B_18439))
      | k1_tarski(B_18439) = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2010,c_4])).

tff(c_6769,plain,
    ( r1_tarski('#skF_9',k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = '#skF_9'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_619,c_6714])).

tff(c_6779,plain,
    ( r1_tarski('#skF_9',k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_6769])).

tff(c_6780,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_6779])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( B_22 = A_21
      | ~ r1_tarski(B_22,A_21)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6788,plain,
    ( k1_tarski('#skF_8') = '#skF_9'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_6780,c_38])).

tff(c_6841,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_6788])).

tff(c_458,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_1'(A_100,B_101),A_100)
      | r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7325,plain,(
    ! [A_18820,B_18821] :
      ( '#skF_1'(k1_tarski(A_18820),B_18821) = A_18820
      | r1_tarski(k1_tarski(A_18820),B_18821) ) ),
    inference(resolution,[status(thm)],[c_458,c_58])).

tff(c_7431,plain,(
    '#skF_1'(k1_tarski('#skF_8'),'#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7325,c_6841])).

tff(c_7507,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_7431,c_4])).

tff(c_7560,plain,(
    r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_7507])).

tff(c_7562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6841,c_7560])).

tff(c_7563,plain,(
    k1_tarski('#skF_8') != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_7564,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_7566,plain,(
    ! [A_30] : k3_xboole_0(A_30,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7564,c_7564,c_50])).

tff(c_8753,plain,(
    ! [D_21770,A_21771,B_21772] :
      ( r2_hidden(D_21770,A_21771)
      | ~ r2_hidden(D_21770,k3_xboole_0(A_21771,B_21772)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8894,plain,(
    ! [D_21911,A_21912] :
      ( r2_hidden(D_21911,A_21912)
      | ~ r2_hidden(D_21911,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7566,c_8753])).

tff(c_9655,plain,(
    ! [B_23963,A_23964] :
      ( r2_hidden('#skF_1'('#skF_9',B_23963),A_23964)
      | r1_tarski('#skF_9',B_23963) ) ),
    inference(resolution,[status(thm)],[c_6,c_8894])).

tff(c_9781,plain,(
    ! [A_24067] : r1_tarski('#skF_9',A_24067) ),
    inference(resolution,[status(thm)],[c_9655,c_4])).

tff(c_48,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_9788,plain,(
    ! [A_24067] : k2_xboole_0('#skF_9',A_24067) = A_24067 ),
    inference(resolution,[status(thm)],[c_9781,c_48])).

tff(c_9790,plain,(
    k1_tarski('#skF_8') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9788,c_90])).

tff(c_9792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7563,c_9790])).

tff(c_9793,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_9794,plain,(
    k1_tarski('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k1_tarski('#skF_8') != '#skF_10'
    | k1_tarski('#skF_8') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_9872,plain,(
    '#skF_10' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9794,c_9794,c_88])).

tff(c_9804,plain,(
    k2_xboole_0('#skF_9','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9794,c_90])).

tff(c_10304,plain,(
    ! [A_24183,C_24184,B_24185] :
      ( r1_tarski(A_24183,k2_xboole_0(C_24184,B_24185))
      | ~ r1_tarski(A_24183,B_24185) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10346,plain,(
    ! [A_24188] :
      ( r1_tarski(A_24188,'#skF_9')
      | ~ r1_tarski(A_24188,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9804,c_10304])).

tff(c_10357,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_10346])).

tff(c_10575,plain,(
    ! [B_24195,A_24196] :
      ( B_24195 = A_24196
      | ~ r1_tarski(B_24195,A_24196)
      | ~ r1_tarski(A_24196,B_24195) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10577,plain,
    ( '#skF_10' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_10357,c_10575])).

tff(c_10590,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_9872,c_10577])).

tff(c_10268,plain,(
    ! [A_24180,B_24181] :
      ( r2_hidden('#skF_1'(A_24180,B_24181),A_24180)
      | r1_tarski(A_24180,B_24181) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9821,plain,(
    ! [C_24138,A_24139] :
      ( C_24138 = A_24139
      | ~ r2_hidden(C_24138,k1_tarski(A_24139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_9828,plain,(
    ! [C_24138] :
      ( C_24138 = '#skF_8'
      | ~ r2_hidden(C_24138,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9794,c_9821])).

tff(c_10297,plain,(
    ! [B_24181] :
      ( '#skF_1'('#skF_9',B_24181) = '#skF_8'
      | r1_tarski('#skF_9',B_24181) ) ),
    inference(resolution,[status(thm)],[c_10268,c_9828])).

tff(c_10608,plain,(
    '#skF_1'('#skF_9','#skF_10') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10297,c_10590])).

tff(c_10628,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | r1_tarski('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_10608,c_4])).

tff(c_10633,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_10590,c_10628])).

tff(c_10424,plain,(
    ! [A_24190,B_24191] : k5_xboole_0(A_24190,k3_xboole_0(A_24190,B_24191)) = k4_xboole_0(A_24190,B_24191) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10448,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = k4_xboole_0(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_10424])).

tff(c_10456,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10448])).

tff(c_10361,plain,(
    k2_xboole_0('#skF_10','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_10357,c_48])).

tff(c_10368,plain,(
    k4_xboole_0('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10361,c_52])).

tff(c_54,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10380,plain,(
    k4_xboole_0('#skF_10',k1_xboole_0) = k3_xboole_0('#skF_10','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10368,c_54])).

tff(c_10457,plain,(
    k3_xboole_0('#skF_10','#skF_9') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10456,c_10380])).

tff(c_10635,plain,(
    ! [D_24197] :
      ( r2_hidden(D_24197,'#skF_9')
      | ~ r2_hidden(D_24197,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10457,c_10])).

tff(c_10651,plain,
    ( r2_hidden('#skF_5'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_36,c_10635])).

tff(c_10657,plain,(
    r2_hidden('#skF_5'('#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_9793,c_10651])).

tff(c_10661,plain,(
    '#skF_5'('#skF_10') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10657,c_9828])).

tff(c_10667,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_10661,c_36])).

tff(c_10671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9793,c_10633,c_10667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.74/2.37  
% 6.74/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.74/2.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_4
% 6.74/2.37  
% 6.74/2.37  %Foreground sorts:
% 6.74/2.37  
% 6.74/2.37  
% 6.74/2.37  %Background operators:
% 6.74/2.37  
% 6.74/2.37  
% 6.74/2.37  %Foreground operators:
% 6.74/2.37  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.74/2.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.74/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.74/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.74/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.74/2.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.74/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.74/2.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.74/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.74/2.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.74/2.37  tff('#skF_10', type, '#skF_10': $i).
% 6.74/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.74/2.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.74/2.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.74/2.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.74/2.38  tff('#skF_9', type, '#skF_9': $i).
% 6.74/2.38  tff('#skF_8', type, '#skF_8': $i).
% 6.74/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.74/2.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.74/2.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.74/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.74/2.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.74/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.74/2.38  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.74/2.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.74/2.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.74/2.38  
% 6.83/2.39  tff(f_135, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.83/2.39  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.83/2.39  tff(f_95, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.83/2.39  tff(f_89, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.83/2.39  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.83/2.39  tff(f_77, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.83/2.39  tff(f_87, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.83/2.39  tff(f_91, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.83/2.39  tff(f_93, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.83/2.39  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.83/2.39  tff(f_102, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.83/2.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.83/2.39  tff(f_114, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.83/2.39  tff(f_83, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.83/2.39  tff(c_84, plain, (k1_xboole_0!='#skF_10' | k1_tarski('#skF_8')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.83/2.39  tff(c_112, plain, (k1_tarski('#skF_8')!='#skF_9'), inference(splitLeft, [status(thm)], [c_84])).
% 6.83/2.39  tff(c_86, plain, (k1_tarski('#skF_8')!='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.83/2.39  tff(c_113, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_86])).
% 6.83/2.39  tff(c_36, plain, (![A_19]: (r2_hidden('#skF_5'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.83/2.39  tff(c_56, plain, (![A_35]: (k5_xboole_0(A_35, k1_xboole_0)=A_35)), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.83/2.39  tff(c_50, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.83/2.39  tff(c_506, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(A_105, B_106))=k4_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.83/2.39  tff(c_524, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=k4_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_506])).
% 6.83/2.39  tff(c_530, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_524])).
% 6.83/2.39  tff(c_42, plain, (![B_22]: (r1_tarski(B_22, B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.83/2.39  tff(c_171, plain, (![A_68, B_69]: (k2_xboole_0(A_68, B_69)=B_69 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.83/2.39  tff(c_180, plain, (![B_70]: (k2_xboole_0(B_70, B_70)=B_70)), inference(resolution, [status(thm)], [c_42, c_171])).
% 6.83/2.39  tff(c_52, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k2_xboole_0(A_31, B_32))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.83/2.39  tff(c_186, plain, (![B_70]: (k4_xboole_0(B_70, B_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_180, c_52])).
% 6.83/2.39  tff(c_332, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k4_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.83/2.39  tff(c_350, plain, (![B_70]: (k4_xboole_0(B_70, k1_xboole_0)=k3_xboole_0(B_70, B_70))), inference(superposition, [status(thm), theory('equality')], [c_186, c_332])).
% 6.83/2.39  tff(c_532, plain, (![B_70]: (k3_xboole_0(B_70, B_70)=B_70)), inference(demodulation, [status(thm), theory('equality')], [c_530, c_350])).
% 6.83/2.39  tff(c_90, plain, (k2_xboole_0('#skF_9', '#skF_10')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.83/2.39  tff(c_128, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k2_xboole_0(A_58, B_59))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.83/2.39  tff(c_135, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_90, c_128])).
% 6.83/2.39  tff(c_353, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k4_xboole_0('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_135, c_332])).
% 6.83/2.39  tff(c_422, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k3_xboole_0('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_353])).
% 6.83/2.39  tff(c_564, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_532, c_422])).
% 6.83/2.39  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.83/2.39  tff(c_663, plain, (![D_113]: (r2_hidden(D_113, k1_tarski('#skF_8')) | ~r2_hidden(D_113, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_564, c_10])).
% 6.83/2.39  tff(c_58, plain, (![C_40, A_36]: (C_40=A_36 | ~r2_hidden(C_40, k1_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.83/2.39  tff(c_673, plain, (![D_114]: (D_114='#skF_8' | ~r2_hidden(D_114, '#skF_9'))), inference(resolution, [status(thm)], [c_663, c_58])).
% 6.83/2.39  tff(c_689, plain, ('#skF_5'('#skF_9')='#skF_8' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_36, c_673])).
% 6.83/2.39  tff(c_695, plain, ('#skF_5'('#skF_9')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_113, c_689])).
% 6.83/2.39  tff(c_699, plain, (r2_hidden('#skF_8', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_695, c_36])).
% 6.83/2.39  tff(c_702, plain, (r2_hidden('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_113, c_699])).
% 6.83/2.39  tff(c_619, plain, (![D_11]: (r2_hidden(D_11, k1_tarski('#skF_8')) | ~r2_hidden(D_11, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_564, c_10])).
% 6.83/2.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.83/2.39  tff(c_690, plain, (![B_2]: ('#skF_1'('#skF_9', B_2)='#skF_8' | r1_tarski('#skF_9', B_2))), inference(resolution, [status(thm)], [c_6, c_673])).
% 6.83/2.39  tff(c_1029, plain, (![B_137, A_138]: (k1_tarski(B_137)=A_138 | k1_xboole_0=A_138 | ~r1_tarski(A_138, k1_tarski(B_137)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.83/2.39  tff(c_1037, plain, (![B_137]: (k1_tarski(B_137)='#skF_9' | k1_xboole_0='#skF_9' | '#skF_1'('#skF_9', k1_tarski(B_137))='#skF_8')), inference(resolution, [status(thm)], [c_690, c_1029])).
% 6.83/2.39  tff(c_2010, plain, (![B_2350]: (k1_tarski(B_2350)='#skF_9' | '#skF_1'('#skF_9', k1_tarski(B_2350))='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_113, c_1037])).
% 6.83/2.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.83/2.39  tff(c_6714, plain, (![B_18439]: (~r2_hidden('#skF_8', k1_tarski(B_18439)) | r1_tarski('#skF_9', k1_tarski(B_18439)) | k1_tarski(B_18439)='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2010, c_4])).
% 6.83/2.39  tff(c_6769, plain, (r1_tarski('#skF_9', k1_tarski('#skF_8')) | k1_tarski('#skF_8')='#skF_9' | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_619, c_6714])).
% 6.83/2.39  tff(c_6779, plain, (r1_tarski('#skF_9', k1_tarski('#skF_8')) | k1_tarski('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_702, c_6769])).
% 6.83/2.39  tff(c_6780, plain, (r1_tarski('#skF_9', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_112, c_6779])).
% 6.83/2.39  tff(c_38, plain, (![B_22, A_21]: (B_22=A_21 | ~r1_tarski(B_22, A_21) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.83/2.39  tff(c_6788, plain, (k1_tarski('#skF_8')='#skF_9' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_6780, c_38])).
% 6.83/2.39  tff(c_6841, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_112, c_6788])).
% 6.83/2.39  tff(c_458, plain, (![A_100, B_101]: (r2_hidden('#skF_1'(A_100, B_101), A_100) | r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.83/2.40  tff(c_7325, plain, (![A_18820, B_18821]: ('#skF_1'(k1_tarski(A_18820), B_18821)=A_18820 | r1_tarski(k1_tarski(A_18820), B_18821))), inference(resolution, [status(thm)], [c_458, c_58])).
% 6.83/2.40  tff(c_7431, plain, ('#skF_1'(k1_tarski('#skF_8'), '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_7325, c_6841])).
% 6.83/2.40  tff(c_7507, plain, (~r2_hidden('#skF_8', '#skF_9') | r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7431, c_4])).
% 6.83/2.40  tff(c_7560, plain, (r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_7507])).
% 6.83/2.40  tff(c_7562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6841, c_7560])).
% 6.83/2.40  tff(c_7563, plain, (k1_tarski('#skF_8')!='#skF_10'), inference(splitRight, [status(thm)], [c_86])).
% 6.83/2.40  tff(c_7564, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_86])).
% 6.83/2.40  tff(c_7566, plain, (![A_30]: (k3_xboole_0(A_30, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7564, c_7564, c_50])).
% 6.83/2.40  tff(c_8753, plain, (![D_21770, A_21771, B_21772]: (r2_hidden(D_21770, A_21771) | ~r2_hidden(D_21770, k3_xboole_0(A_21771, B_21772)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.83/2.40  tff(c_8894, plain, (![D_21911, A_21912]: (r2_hidden(D_21911, A_21912) | ~r2_hidden(D_21911, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_7566, c_8753])).
% 6.83/2.40  tff(c_9655, plain, (![B_23963, A_23964]: (r2_hidden('#skF_1'('#skF_9', B_23963), A_23964) | r1_tarski('#skF_9', B_23963))), inference(resolution, [status(thm)], [c_6, c_8894])).
% 6.83/2.40  tff(c_9781, plain, (![A_24067]: (r1_tarski('#skF_9', A_24067))), inference(resolution, [status(thm)], [c_9655, c_4])).
% 6.83/2.40  tff(c_48, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.83/2.40  tff(c_9788, plain, (![A_24067]: (k2_xboole_0('#skF_9', A_24067)=A_24067)), inference(resolution, [status(thm)], [c_9781, c_48])).
% 6.83/2.40  tff(c_9790, plain, (k1_tarski('#skF_8')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_9788, c_90])).
% 6.83/2.40  tff(c_9792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7563, c_9790])).
% 6.83/2.40  tff(c_9793, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_84])).
% 6.83/2.40  tff(c_9794, plain, (k1_tarski('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 6.83/2.40  tff(c_88, plain, (k1_tarski('#skF_8')!='#skF_10' | k1_tarski('#skF_8')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.83/2.40  tff(c_9872, plain, ('#skF_10'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9794, c_9794, c_88])).
% 6.83/2.40  tff(c_9804, plain, (k2_xboole_0('#skF_9', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9794, c_90])).
% 6.83/2.40  tff(c_10304, plain, (![A_24183, C_24184, B_24185]: (r1_tarski(A_24183, k2_xboole_0(C_24184, B_24185)) | ~r1_tarski(A_24183, B_24185))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.83/2.40  tff(c_10346, plain, (![A_24188]: (r1_tarski(A_24188, '#skF_9') | ~r1_tarski(A_24188, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_9804, c_10304])).
% 6.83/2.40  tff(c_10357, plain, (r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_42, c_10346])).
% 6.83/2.40  tff(c_10575, plain, (![B_24195, A_24196]: (B_24195=A_24196 | ~r1_tarski(B_24195, A_24196) | ~r1_tarski(A_24196, B_24195))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.83/2.40  tff(c_10577, plain, ('#skF_10'='#skF_9' | ~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_10357, c_10575])).
% 6.83/2.40  tff(c_10590, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_9872, c_10577])).
% 6.83/2.40  tff(c_10268, plain, (![A_24180, B_24181]: (r2_hidden('#skF_1'(A_24180, B_24181), A_24180) | r1_tarski(A_24180, B_24181))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.83/2.40  tff(c_9821, plain, (![C_24138, A_24139]: (C_24138=A_24139 | ~r2_hidden(C_24138, k1_tarski(A_24139)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.83/2.40  tff(c_9828, plain, (![C_24138]: (C_24138='#skF_8' | ~r2_hidden(C_24138, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9794, c_9821])).
% 6.83/2.40  tff(c_10297, plain, (![B_24181]: ('#skF_1'('#skF_9', B_24181)='#skF_8' | r1_tarski('#skF_9', B_24181))), inference(resolution, [status(thm)], [c_10268, c_9828])).
% 6.83/2.40  tff(c_10608, plain, ('#skF_1'('#skF_9', '#skF_10')='#skF_8'), inference(resolution, [status(thm)], [c_10297, c_10590])).
% 6.83/2.40  tff(c_10628, plain, (~r2_hidden('#skF_8', '#skF_10') | r1_tarski('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_10608, c_4])).
% 6.83/2.40  tff(c_10633, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_10590, c_10628])).
% 6.83/2.40  tff(c_10424, plain, (![A_24190, B_24191]: (k5_xboole_0(A_24190, k3_xboole_0(A_24190, B_24191))=k4_xboole_0(A_24190, B_24191))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.83/2.40  tff(c_10448, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=k4_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_10424])).
% 6.83/2.40  tff(c_10456, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_10448])).
% 6.83/2.40  tff(c_10361, plain, (k2_xboole_0('#skF_10', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_10357, c_48])).
% 6.83/2.40  tff(c_10368, plain, (k4_xboole_0('#skF_10', '#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10361, c_52])).
% 6.83/2.40  tff(c_54, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.83/2.40  tff(c_10380, plain, (k4_xboole_0('#skF_10', k1_xboole_0)=k3_xboole_0('#skF_10', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10368, c_54])).
% 6.83/2.40  tff(c_10457, plain, (k3_xboole_0('#skF_10', '#skF_9')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_10456, c_10380])).
% 6.83/2.40  tff(c_10635, plain, (![D_24197]: (r2_hidden(D_24197, '#skF_9') | ~r2_hidden(D_24197, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_10457, c_10])).
% 6.83/2.40  tff(c_10651, plain, (r2_hidden('#skF_5'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_36, c_10635])).
% 6.83/2.40  tff(c_10657, plain, (r2_hidden('#skF_5'('#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_9793, c_10651])).
% 6.83/2.40  tff(c_10661, plain, ('#skF_5'('#skF_10')='#skF_8'), inference(resolution, [status(thm)], [c_10657, c_9828])).
% 6.83/2.40  tff(c_10667, plain, (r2_hidden('#skF_8', '#skF_10') | k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_10661, c_36])).
% 6.83/2.40  tff(c_10671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9793, c_10633, c_10667])).
% 6.83/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.40  
% 6.83/2.40  Inference rules
% 6.83/2.40  ----------------------
% 6.83/2.40  #Ref     : 0
% 6.83/2.40  #Sup     : 2167
% 6.83/2.40  #Fact    : 4
% 6.83/2.40  #Define  : 0
% 6.83/2.40  #Split   : 11
% 6.83/2.40  #Chain   : 0
% 6.83/2.40  #Close   : 0
% 6.83/2.40  
% 6.83/2.40  Ordering : KBO
% 6.83/2.40  
% 6.83/2.40  Simplification rules
% 6.83/2.40  ----------------------
% 6.83/2.40  #Subsume      : 391
% 6.83/2.40  #Demod        : 461
% 6.83/2.40  #Tautology    : 616
% 6.83/2.40  #SimpNegUnit  : 48
% 6.83/2.40  #BackRed      : 47
% 6.83/2.40  
% 6.83/2.40  #Partial instantiations: 13980
% 6.83/2.40  #Strategies tried      : 1
% 6.83/2.40  
% 6.83/2.40  Timing (in seconds)
% 6.83/2.40  ----------------------
% 6.83/2.40  Preprocessing        : 0.33
% 6.83/2.40  Parsing              : 0.16
% 6.83/2.40  CNF conversion       : 0.03
% 6.83/2.40  Main loop            : 1.24
% 6.83/2.40  Inferencing          : 0.54
% 6.83/2.40  Reduction            : 0.34
% 6.83/2.40  Demodulation         : 0.24
% 6.83/2.40  BG Simplification    : 0.05
% 6.83/2.40  Subsumption          : 0.21
% 6.83/2.40  Abstraction          : 0.05
% 6.83/2.40  MUC search           : 0.00
% 6.83/2.40  Cooper               : 0.00
% 6.83/2.40  Total                : 1.62
% 6.83/2.40  Index Insertion      : 0.00
% 6.83/2.40  Index Deletion       : 0.00
% 6.83/2.40  Index Matching       : 0.00
% 6.83/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
