%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:18 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 268 expanded)
%              Number of leaves         :   36 ( 101 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 587 expanded)
%              Number of equality atoms :   47 ( 276 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_66,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_280,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_2'(A_96,B_97),A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_289,plain,(
    ! [A_96,B_97] :
      ( ~ v1_xboole_0(A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_280,c_2])).

tff(c_213,plain,(
    ! [A_84,B_85] :
      ( r1_xboole_0(k1_tarski(A_84),B_85)
      | r2_hidden(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_220,plain,(
    ! [B_85,A_84] :
      ( r1_xboole_0(B_85,k1_tarski(A_84))
      | r2_hidden(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_213,c_12])).

tff(c_70,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_385,plain,(
    ! [A_108,C_109,B_110] :
      ( r1_xboole_0(A_108,C_109)
      | ~ r1_xboole_0(A_108,k2_xboole_0(B_110,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_414,plain,(
    ! [A_113] :
      ( r1_xboole_0(A_113,'#skF_5')
      | ~ r1_xboole_0(A_113,k1_tarski('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_385])).

tff(c_425,plain,(
    ! [B_114] :
      ( r1_xboole_0(B_114,'#skF_5')
      | r2_hidden('#skF_3',B_114) ) ),
    inference(resolution,[status(thm)],[c_220,c_414])).

tff(c_52,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tarski(A_52),B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_75,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_34,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_86,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_34])).

tff(c_238,plain,(
    ! [B_90,A_91] :
      ( B_90 = A_91
      | ~ r1_tarski(B_90,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_242,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_238])).

tff(c_252,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_242])).

tff(c_262,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_252])).

tff(c_437,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_425,c_262])).

tff(c_475,plain,(
    ! [B_117,A_118] :
      ( ~ r1_xboole_0(B_117,A_118)
      | ~ r1_tarski(B_117,A_118)
      | v1_xboole_0(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_500,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_437,c_475])).

tff(c_524,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_538,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_289,c_524])).

tff(c_18,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_544,plain,(
    ! [A_120,B_121,C_122] :
      ( r1_xboole_0(A_120,B_121)
      | ~ r1_xboole_0(A_120,k2_xboole_0(B_121,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_618,plain,(
    ! [A_125] :
      ( r1_xboole_0(A_125,'#skF_4')
      | ~ r1_xboole_0(A_125,k1_tarski('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_544])).

tff(c_716,plain,(
    ! [B_128] :
      ( r1_xboole_0(B_128,'#skF_4')
      | r2_hidden('#skF_3',B_128) ) ),
    inference(resolution,[status(thm)],[c_220,c_618])).

tff(c_729,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_716,c_262])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( ~ r1_xboole_0(B_18,A_17)
      | ~ r1_tarski(B_18,A_17)
      | v1_xboole_0(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_757,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_729,c_26])).

tff(c_767,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_757])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_767])).

tff(c_770,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_57] : r1_tarski(k1_xboole_0,k1_tarski(B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_268,plain,(
    ! [B_94] :
      ( k1_tarski(B_94) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_94),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_60,c_238])).

tff(c_274,plain,(
    ! [A_95] :
      ( k1_tarski(A_95) = k1_xboole_0
      | ~ r2_hidden(A_95,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_268])).

tff(c_279,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_274])).

tff(c_312,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_290,plain,(
    ! [A_98,B_99] :
      ( ~ v1_xboole_0(A_98)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_280,c_2])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_310,plain,(
    ! [A_98,B_99] :
      ( k2_xboole_0(A_98,B_99) = B_99
      | ~ v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_290,c_20])).

tff(c_324,plain,(
    ! [B_104] : k2_xboole_0(k1_xboole_0,B_104) = B_104 ),
    inference(resolution,[status(thm)],[c_312,c_310])).

tff(c_347,plain,(
    ! [B_105] : r1_tarski(k1_xboole_0,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_34])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_356,plain,(
    ! [B_106] :
      ( k1_xboole_0 = B_106
      | ~ r1_tarski(B_106,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_347,c_14])).

tff(c_375,plain,(
    ! [A_96] :
      ( k1_xboole_0 = A_96
      | ~ v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_289,c_356])).

tff(c_774,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_770,c_375])).

tff(c_780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_774])).

tff(c_782,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_22,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_860,plain,(
    ! [B_136,A_137] :
      ( ~ r1_xboole_0(B_136,A_137)
      | ~ r1_tarski(B_136,A_137)
      | v1_xboole_0(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_866,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_860])).

tff(c_871,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_866])).

tff(c_873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_782,c_871])).

tff(c_874,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_875,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_878,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_875,c_22])).

tff(c_1298,plain,(
    ! [B_199,A_200] :
      ( ~ r1_xboole_0(B_199,A_200)
      | ~ r1_tarski(B_199,A_200)
      | v1_xboole_0(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1325,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_878,c_1298])).

tff(c_1341,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1325])).

tff(c_1074,plain,(
    ! [A_176,B_177] :
      ( r2_hidden('#skF_2'(A_176,B_177),A_176)
      | r1_tarski(A_176,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1085,plain,(
    ! [A_178,B_179] :
      ( ~ v1_xboole_0(A_178)
      | r1_tarski(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_1074,c_2])).

tff(c_1094,plain,(
    ! [A_178,B_179] :
      ( k2_xboole_0(A_178,B_179) = B_179
      | ~ v1_xboole_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_1085,c_20])).

tff(c_1344,plain,(
    ! [B_179] : k2_xboole_0('#skF_4',B_179) = B_179 ),
    inference(resolution,[status(thm)],[c_1341,c_1094])).

tff(c_1350,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_70])).

tff(c_1352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_874,c_1350])).

tff(c_1354,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1389,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_1354,c_68])).

tff(c_1379,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_70])).

tff(c_1460,plain,(
    ! [A_216,B_217] :
      ( r1_xboole_0(k1_tarski(A_216),B_217)
      | r2_hidden(A_216,B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1469,plain,(
    ! [B_217] :
      ( r1_xboole_0('#skF_4',B_217)
      | r2_hidden('#skF_3',B_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1354,c_1460])).

tff(c_1525,plain,(
    ! [A_224,B_225] :
      ( r1_tarski(k1_tarski(A_224),B_225)
      | ~ r2_hidden(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1540,plain,(
    ! [B_227] :
      ( r1_tarski('#skF_4',B_227)
      | ~ r2_hidden('#skF_3',B_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1354,c_1525])).

tff(c_1733,plain,(
    ! [B_241] :
      ( r1_tarski('#skF_4',B_241)
      | r1_xboole_0('#skF_4',B_241) ) ),
    inference(resolution,[status(thm)],[c_1469,c_1540])).

tff(c_1740,plain,(
    ! [B_241] :
      ( r1_xboole_0(B_241,'#skF_4')
      | r1_tarski('#skF_4',B_241) ) ),
    inference(resolution,[status(thm)],[c_1733,c_12])).

tff(c_1353,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1817,plain,(
    ! [A_247,C_248,B_249] :
      ( r1_xboole_0(A_247,C_248)
      | ~ r1_xboole_0(A_247,k2_xboole_0(B_249,C_248)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1845,plain,(
    ! [A_250] :
      ( r1_xboole_0(A_250,'#skF_5')
      | ~ r1_xboole_0(A_250,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_1817])).

tff(c_24,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1851,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1845,c_24])).

tff(c_1855,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1353,c_1851])).

tff(c_1862,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1740,c_1855])).

tff(c_1868,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1862,c_20])).

tff(c_1876,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_1868])).

tff(c_1878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1389,c_1876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:31:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.57  
% 3.40/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.40/1.57  
% 3.40/1.57  %Foreground sorts:
% 3.40/1.57  
% 3.40/1.57  
% 3.40/1.57  %Background operators:
% 3.40/1.57  
% 3.40/1.57  
% 3.40/1.57  %Foreground operators:
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.40/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.40/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.40/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.57  
% 3.40/1.59  tff(f_140, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.40/1.59  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.40/1.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.40/1.59  tff(f_113, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.40/1.59  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.40/1.59  tff(f_88, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.40/1.59  tff(f_108, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.40/1.59  tff(f_90, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.40/1.59  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.40/1.59  tff(f_72, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.40/1.59  tff(f_119, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.40/1.59  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.40/1.59  tff(f_64, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.40/1.59  tff(c_66, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.40/1.59  tff(c_90, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 3.40/1.59  tff(c_280, plain, (![A_96, B_97]: (r2_hidden('#skF_2'(A_96, B_97), A_96) | r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.59  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.59  tff(c_289, plain, (![A_96, B_97]: (~v1_xboole_0(A_96) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_280, c_2])).
% 3.40/1.59  tff(c_213, plain, (![A_84, B_85]: (r1_xboole_0(k1_tarski(A_84), B_85) | r2_hidden(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.40/1.59  tff(c_12, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.59  tff(c_220, plain, (![B_85, A_84]: (r1_xboole_0(B_85, k1_tarski(A_84)) | r2_hidden(A_84, B_85))), inference(resolution, [status(thm)], [c_213, c_12])).
% 3.40/1.59  tff(c_70, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.40/1.59  tff(c_385, plain, (![A_108, C_109, B_110]: (r1_xboole_0(A_108, C_109) | ~r1_xboole_0(A_108, k2_xboole_0(B_110, C_109)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.40/1.59  tff(c_414, plain, (![A_113]: (r1_xboole_0(A_113, '#skF_5') | ~r1_xboole_0(A_113, k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_385])).
% 3.40/1.59  tff(c_425, plain, (![B_114]: (r1_xboole_0(B_114, '#skF_5') | r2_hidden('#skF_3', B_114))), inference(resolution, [status(thm)], [c_220, c_414])).
% 3.40/1.59  tff(c_52, plain, (![A_52, B_53]: (r1_tarski(k1_tarski(A_52), B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.40/1.59  tff(c_64, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.40/1.59  tff(c_75, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 3.40/1.59  tff(c_34, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.40/1.59  tff(c_86, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_34])).
% 3.40/1.59  tff(c_238, plain, (![B_90, A_91]: (B_90=A_91 | ~r1_tarski(B_90, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.59  tff(c_242, plain, (k1_tarski('#skF_3')='#skF_4' | ~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_86, c_238])).
% 3.40/1.59  tff(c_252, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_75, c_242])).
% 3.40/1.59  tff(c_262, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_252])).
% 3.40/1.59  tff(c_437, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_425, c_262])).
% 3.40/1.59  tff(c_475, plain, (![B_117, A_118]: (~r1_xboole_0(B_117, A_118) | ~r1_tarski(B_117, A_118) | v1_xboole_0(B_117))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.59  tff(c_500, plain, (~r1_tarski('#skF_4', '#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_437, c_475])).
% 3.40/1.59  tff(c_524, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_500])).
% 3.40/1.59  tff(c_538, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_289, c_524])).
% 3.40/1.59  tff(c_18, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.59  tff(c_544, plain, (![A_120, B_121, C_122]: (r1_xboole_0(A_120, B_121) | ~r1_xboole_0(A_120, k2_xboole_0(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.40/1.59  tff(c_618, plain, (![A_125]: (r1_xboole_0(A_125, '#skF_4') | ~r1_xboole_0(A_125, k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_544])).
% 3.40/1.59  tff(c_716, plain, (![B_128]: (r1_xboole_0(B_128, '#skF_4') | r2_hidden('#skF_3', B_128))), inference(resolution, [status(thm)], [c_220, c_618])).
% 3.40/1.59  tff(c_729, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_716, c_262])).
% 3.40/1.59  tff(c_26, plain, (![B_18, A_17]: (~r1_xboole_0(B_18, A_17) | ~r1_tarski(B_18, A_17) | v1_xboole_0(B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.59  tff(c_757, plain, (~r1_tarski('#skF_4', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_729, c_26])).
% 3.40/1.59  tff(c_767, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_757])).
% 3.40/1.59  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_538, c_767])).
% 3.40/1.59  tff(c_770, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_500])).
% 3.40/1.59  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.59  tff(c_60, plain, (![B_57]: (r1_tarski(k1_xboole_0, k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.40/1.59  tff(c_268, plain, (![B_94]: (k1_tarski(B_94)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_94), k1_xboole_0))), inference(resolution, [status(thm)], [c_60, c_238])).
% 3.40/1.59  tff(c_274, plain, (![A_95]: (k1_tarski(A_95)=k1_xboole_0 | ~r2_hidden(A_95, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_268])).
% 3.40/1.59  tff(c_279, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_274])).
% 3.40/1.59  tff(c_312, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_279])).
% 3.40/1.59  tff(c_290, plain, (![A_98, B_99]: (~v1_xboole_0(A_98) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_280, c_2])).
% 3.40/1.59  tff(c_20, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.59  tff(c_310, plain, (![A_98, B_99]: (k2_xboole_0(A_98, B_99)=B_99 | ~v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_290, c_20])).
% 3.40/1.59  tff(c_324, plain, (![B_104]: (k2_xboole_0(k1_xboole_0, B_104)=B_104)), inference(resolution, [status(thm)], [c_312, c_310])).
% 3.40/1.59  tff(c_347, plain, (![B_105]: (r1_tarski(k1_xboole_0, B_105))), inference(superposition, [status(thm), theory('equality')], [c_324, c_34])).
% 3.40/1.59  tff(c_14, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.59  tff(c_356, plain, (![B_106]: (k1_xboole_0=B_106 | ~r1_tarski(B_106, k1_xboole_0))), inference(resolution, [status(thm)], [c_347, c_14])).
% 3.40/1.59  tff(c_375, plain, (![A_96]: (k1_xboole_0=A_96 | ~v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_289, c_356])).
% 3.40/1.59  tff(c_774, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_770, c_375])).
% 3.40/1.59  tff(c_780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_774])).
% 3.40/1.59  tff(c_782, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_279])).
% 3.40/1.59  tff(c_22, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.40/1.59  tff(c_860, plain, (![B_136, A_137]: (~r1_xboole_0(B_136, A_137) | ~r1_tarski(B_136, A_137) | v1_xboole_0(B_136))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.59  tff(c_866, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_860])).
% 3.40/1.59  tff(c_871, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_866])).
% 3.40/1.59  tff(c_873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_782, c_871])).
% 3.40/1.59  tff(c_874, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_66])).
% 3.40/1.59  tff(c_875, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 3.40/1.59  tff(c_878, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_875, c_875, c_22])).
% 3.40/1.59  tff(c_1298, plain, (![B_199, A_200]: (~r1_xboole_0(B_199, A_200) | ~r1_tarski(B_199, A_200) | v1_xboole_0(B_199))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.59  tff(c_1325, plain, (~r1_tarski('#skF_4', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_878, c_1298])).
% 3.40/1.59  tff(c_1341, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1325])).
% 3.40/1.59  tff(c_1074, plain, (![A_176, B_177]: (r2_hidden('#skF_2'(A_176, B_177), A_176) | r1_tarski(A_176, B_177))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.59  tff(c_1085, plain, (![A_178, B_179]: (~v1_xboole_0(A_178) | r1_tarski(A_178, B_179))), inference(resolution, [status(thm)], [c_1074, c_2])).
% 3.40/1.59  tff(c_1094, plain, (![A_178, B_179]: (k2_xboole_0(A_178, B_179)=B_179 | ~v1_xboole_0(A_178))), inference(resolution, [status(thm)], [c_1085, c_20])).
% 3.40/1.59  tff(c_1344, plain, (![B_179]: (k2_xboole_0('#skF_4', B_179)=B_179)), inference(resolution, [status(thm)], [c_1341, c_1094])).
% 3.40/1.59  tff(c_1350, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1344, c_70])).
% 3.40/1.59  tff(c_1352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_874, c_1350])).
% 3.40/1.59  tff(c_1354, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 3.40/1.59  tff(c_68, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.40/1.59  tff(c_1389, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1354, c_1354, c_68])).
% 3.40/1.59  tff(c_1379, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1354, c_70])).
% 3.40/1.59  tff(c_1460, plain, (![A_216, B_217]: (r1_xboole_0(k1_tarski(A_216), B_217) | r2_hidden(A_216, B_217))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.40/1.59  tff(c_1469, plain, (![B_217]: (r1_xboole_0('#skF_4', B_217) | r2_hidden('#skF_3', B_217))), inference(superposition, [status(thm), theory('equality')], [c_1354, c_1460])).
% 3.40/1.59  tff(c_1525, plain, (![A_224, B_225]: (r1_tarski(k1_tarski(A_224), B_225) | ~r2_hidden(A_224, B_225))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.40/1.59  tff(c_1540, plain, (![B_227]: (r1_tarski('#skF_4', B_227) | ~r2_hidden('#skF_3', B_227))), inference(superposition, [status(thm), theory('equality')], [c_1354, c_1525])).
% 3.40/1.59  tff(c_1733, plain, (![B_241]: (r1_tarski('#skF_4', B_241) | r1_xboole_0('#skF_4', B_241))), inference(resolution, [status(thm)], [c_1469, c_1540])).
% 3.40/1.59  tff(c_1740, plain, (![B_241]: (r1_xboole_0(B_241, '#skF_4') | r1_tarski('#skF_4', B_241))), inference(resolution, [status(thm)], [c_1733, c_12])).
% 3.40/1.59  tff(c_1353, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 3.40/1.59  tff(c_1817, plain, (![A_247, C_248, B_249]: (r1_xboole_0(A_247, C_248) | ~r1_xboole_0(A_247, k2_xboole_0(B_249, C_248)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.40/1.59  tff(c_1845, plain, (![A_250]: (r1_xboole_0(A_250, '#skF_5') | ~r1_xboole_0(A_250, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1379, c_1817])).
% 3.40/1.59  tff(c_24, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.40/1.59  tff(c_1851, plain, (k1_xboole_0='#skF_5' | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1845, c_24])).
% 3.40/1.59  tff(c_1855, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1353, c_1851])).
% 3.40/1.59  tff(c_1862, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1740, c_1855])).
% 3.40/1.59  tff(c_1868, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_1862, c_20])).
% 3.40/1.59  tff(c_1876, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_1868])).
% 3.40/1.59  tff(c_1878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1389, c_1876])).
% 3.40/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.59  
% 3.40/1.59  Inference rules
% 3.40/1.59  ----------------------
% 3.40/1.59  #Ref     : 0
% 3.40/1.59  #Sup     : 400
% 3.40/1.59  #Fact    : 0
% 3.40/1.59  #Define  : 0
% 3.40/1.59  #Split   : 9
% 3.40/1.59  #Chain   : 0
% 3.40/1.59  #Close   : 0
% 3.40/1.59  
% 3.40/1.59  Ordering : KBO
% 3.40/1.59  
% 3.40/1.59  Simplification rules
% 3.40/1.59  ----------------------
% 3.40/1.59  #Subsume      : 62
% 3.40/1.59  #Demod        : 116
% 3.40/1.59  #Tautology    : 169
% 3.40/1.59  #SimpNegUnit  : 25
% 3.40/1.59  #BackRed      : 8
% 3.40/1.59  
% 3.40/1.59  #Partial instantiations: 0
% 3.40/1.59  #Strategies tried      : 1
% 3.40/1.59  
% 3.40/1.59  Timing (in seconds)
% 3.40/1.59  ----------------------
% 3.40/1.59  Preprocessing        : 0.34
% 3.40/1.59  Parsing              : 0.18
% 3.40/1.59  CNF conversion       : 0.02
% 3.40/1.59  Main loop            : 0.46
% 3.40/1.59  Inferencing          : 0.18
% 3.40/1.59  Reduction            : 0.14
% 3.40/1.59  Demodulation         : 0.10
% 3.40/1.59  BG Simplification    : 0.02
% 3.40/1.59  Subsumption          : 0.08
% 3.40/1.59  Abstraction          : 0.02
% 3.40/1.59  MUC search           : 0.00
% 3.40/1.59  Cooper               : 0.00
% 3.40/1.59  Total                : 0.84
% 3.40/1.59  Index Insertion      : 0.00
% 3.40/1.59  Index Deletion       : 0.00
% 3.40/1.59  Index Matching       : 0.00
% 3.40/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
