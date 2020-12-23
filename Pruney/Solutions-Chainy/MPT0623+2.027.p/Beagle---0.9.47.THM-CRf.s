%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:09 EST 2020

% Result     : Theorem 8.55s
% Output     : CNFRefutation 8.78s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 335 expanded)
%              Number of leaves         :   38 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  206 ( 883 expanded)
%              Number of equality atoms :   91 ( 407 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_102,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_141,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_123,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_64,plain,(
    ! [A_45] : v1_relat_1('#skF_10'(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_62,plain,(
    ! [A_45] : v1_funct_1('#skF_10'(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_60,plain,(
    ! [A_45] : k1_relat_1('#skF_10'(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_78,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_101,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2332,plain,(
    ! [A_3132,B_3133] :
      ( r2_hidden(k4_tarski('#skF_5'(A_3132,B_3133),'#skF_6'(A_3132,B_3133)),A_3132)
      | r2_hidden('#skF_7'(A_3132,B_3133),B_3133)
      | k1_relat_1(A_3132) = B_3133 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_260,plain,(
    ! [C_104,A_105,D_106] :
      ( r2_hidden(C_104,k1_relat_1(A_105))
      | ~ r2_hidden(k4_tarski(C_104,D_106),A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_266,plain,(
    ! [C_107,D_108] : r2_hidden(C_107,k1_relat_1(k1_tarski(k4_tarski(C_107,D_108)))) ),
    inference(resolution,[status(thm)],[c_20,c_260])).

tff(c_32,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k1_relat_1(A_18))
      | ~ r2_hidden(k4_tarski(C_33,D_36),A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_271,plain,(
    ! [C_33,D_36,D_108] : r2_hidden(C_33,k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(C_33,D_36),D_108))))) ),
    inference(resolution,[status(thm)],[c_266,c_32])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_272,plain,(
    ! [C_109,B_110,A_111] :
      ( r2_hidden(C_109,B_110)
      | ~ r2_hidden(C_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1051,plain,(
    ! [A_1730,B_1731,B_1732] :
      ( r2_hidden('#skF_2'(A_1730,B_1731),B_1732)
      | ~ r1_tarski(B_1731,B_1732)
      | r1_xboole_0(A_1730,B_1731) ) ),
    inference(resolution,[status(thm)],[c_10,c_272])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_296,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_xboole_0(A_116,B_117)
      | ~ r2_hidden(C_118,B_117)
      | ~ r2_hidden(C_118,A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_299,plain,(
    ! [C_118,A_12] :
      ( ~ r2_hidden(C_118,k1_xboole_0)
      | ~ r2_hidden(C_118,A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_296])).

tff(c_1311,plain,(
    ! [A_2107,B_2108,A_2109] :
      ( ~ r2_hidden('#skF_2'(A_2107,B_2108),A_2109)
      | ~ r1_tarski(B_2108,k1_xboole_0)
      | r1_xboole_0(A_2107,B_2108) ) ),
    inference(resolution,[status(thm)],[c_1051,c_299])).

tff(c_1351,plain,(
    ! [B_2139,A_2140] :
      ( ~ r1_tarski(B_2139,k1_xboole_0)
      | r1_xboole_0(A_2140,B_2139) ) ),
    inference(resolution,[status(thm)],[c_271,c_1311])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1394,plain,(
    ! [C_2232,B_2233,A_2234] :
      ( ~ r2_hidden(C_2232,B_2233)
      | ~ r2_hidden(C_2232,A_2234)
      | ~ r1_tarski(B_2233,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1351,c_8])).

tff(c_1434,plain,(
    ! [C_2264,A_2265] :
      ( ~ r2_hidden(C_2264,A_2265)
      | ~ r1_tarski(k1_tarski(C_2264),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_1394])).

tff(c_1468,plain,(
    ! [C_33] : ~ r1_tarski(k1_tarski(C_33),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_271,c_1434])).

tff(c_197,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),A_89)
      | r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_202,plain,(
    ! [A_13,B_90] :
      ( '#skF_1'(k1_tarski(A_13),B_90) = A_13
      | r1_tarski(k1_tarski(A_13),B_90) ) ),
    inference(resolution,[status(thm)],[c_197,c_18])).

tff(c_1511,plain,(
    ! [C_2326] : ~ r1_tarski(k1_tarski(C_2326),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_271,c_1434])).

tff(c_1526,plain,(
    ! [A_2387] : '#skF_1'(k1_tarski(A_2387),k1_xboole_0) = A_2387 ),
    inference(resolution,[status(thm)],[c_202,c_1511])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1538,plain,(
    ! [A_2387] :
      ( ~ r2_hidden(A_2387,k1_xboole_0)
      | r1_tarski(k1_tarski(A_2387),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_4])).

tff(c_1601,plain,(
    ! [A_2387] : ~ r2_hidden(A_2387,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1468,c_1538])).

tff(c_2347,plain,(
    ! [B_3133] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_3133),B_3133)
      | k1_relat_1(k1_xboole_0) = B_3133 ) ),
    inference(resolution,[status(thm)],[c_2332,c_1601])).

tff(c_2364,plain,(
    ! [B_3133] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_3133),B_3133)
      | k1_xboole_0 = B_3133 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2347])).

tff(c_70,plain,(
    ! [A_53,B_57] :
      ( k1_relat_1('#skF_11'(A_53,B_57)) = A_53
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_72,plain,(
    ! [A_53,B_57] :
      ( v1_funct_1('#skF_11'(A_53,B_57))
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_74,plain,(
    ! [A_53,B_57] :
      ( v1_relat_1('#skF_11'(A_53,B_57))
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_694,plain,(
    ! [A_1482,B_1483] :
      ( '#skF_1'(k1_tarski(A_1482),B_1483) = A_1482
      | r1_tarski(k1_tarski(A_1482),B_1483) ) ),
    inference(resolution,[status(thm)],[c_197,c_18])).

tff(c_211,plain,(
    ! [A_94,B_95] :
      ( k2_relat_1('#skF_11'(A_94,B_95)) = k1_tarski(B_95)
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_76,plain,(
    ! [C_60] :
      ( ~ r1_tarski(k2_relat_1(C_60),'#skF_12')
      | k1_relat_1(C_60) != '#skF_13'
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_217,plain,(
    ! [B_95,A_94] :
      ( ~ r1_tarski(k1_tarski(B_95),'#skF_12')
      | k1_relat_1('#skF_11'(A_94,B_95)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_94,B_95))
      | ~ v1_relat_1('#skF_11'(A_94,B_95))
      | k1_xboole_0 = A_94 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_76])).

tff(c_1065,plain,(
    ! [A_1762,A_1763] :
      ( k1_relat_1('#skF_11'(A_1762,A_1763)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_1762,A_1763))
      | ~ v1_relat_1('#skF_11'(A_1762,A_1763))
      | k1_xboole_0 = A_1762
      | '#skF_1'(k1_tarski(A_1763),'#skF_12') = A_1763 ) ),
    inference(resolution,[status(thm)],[c_694,c_217])).

tff(c_1369,plain,(
    ! [A_2201,B_2202] :
      ( k1_relat_1('#skF_11'(A_2201,B_2202)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_2201,B_2202))
      | '#skF_1'(k1_tarski(B_2202),'#skF_12') = B_2202
      | k1_xboole_0 = A_2201 ) ),
    inference(resolution,[status(thm)],[c_74,c_1065])).

tff(c_5753,plain,(
    ! [A_5983,B_5984] :
      ( k1_relat_1('#skF_11'(A_5983,B_5984)) != '#skF_13'
      | '#skF_1'(k1_tarski(B_5984),'#skF_12') = B_5984
      | k1_xboole_0 = A_5983 ) ),
    inference(resolution,[status(thm)],[c_72,c_1369])).

tff(c_5777,plain,(
    ! [A_53,B_57] :
      ( A_53 != '#skF_13'
      | '#skF_1'(k1_tarski(B_57),'#skF_12') = B_57
      | k1_xboole_0 = A_53
      | k1_xboole_0 = A_53 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_5753])).

tff(c_10276,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_5777])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [A_82] :
      ( k2_relat_1(A_82) = k1_xboole_0
      | k1_relat_1(A_82) != k1_xboole_0
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_147,plain,(
    ! [A_45] :
      ( k2_relat_1('#skF_10'(A_45)) = k1_xboole_0
      | k1_relat_1('#skF_10'(A_45)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_64,c_138])).

tff(c_154,plain,(
    ! [A_83] :
      ( k2_relat_1('#skF_10'(A_83)) = k1_xboole_0
      | k1_xboole_0 != A_83 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_147])).

tff(c_160,plain,(
    ! [A_83] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_12')
      | k1_relat_1('#skF_10'(A_83)) != '#skF_13'
      | ~ v1_funct_1('#skF_10'(A_83))
      | ~ v1_relat_1('#skF_10'(A_83))
      | k1_xboole_0 != A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_76])).

tff(c_166,plain,(
    ! [A_83] :
      ( A_83 != '#skF_13'
      | k1_xboole_0 != A_83 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_14,c_160])).

tff(c_171,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_166])).

tff(c_10459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10276,c_171])).

tff(c_10464,plain,(
    ! [B_8640] : '#skF_1'(k1_tarski(B_8640),'#skF_12') = B_8640 ),
    inference(splitRight,[status(thm)],[c_5777])).

tff(c_10545,plain,(
    ! [B_8670] :
      ( ~ r2_hidden(B_8670,'#skF_12')
      | r1_tarski(k1_tarski(B_8670),'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10464,c_4])).

tff(c_10671,plain,(
    ! [A_8731,B_8732] :
      ( k1_relat_1('#skF_11'(A_8731,B_8732)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_8731,B_8732))
      | ~ v1_relat_1('#skF_11'(A_8731,B_8732))
      | k1_xboole_0 = A_8731
      | ~ r2_hidden(B_8732,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_10545,c_217])).

tff(c_10952,plain,(
    ! [A_8886,B_8887] :
      ( k1_relat_1('#skF_11'(A_8886,B_8887)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_8886,B_8887))
      | ~ r2_hidden(B_8887,'#skF_12')
      | k1_xboole_0 = A_8886 ) ),
    inference(resolution,[status(thm)],[c_74,c_10671])).

tff(c_10958,plain,(
    ! [A_8917,B_8918] :
      ( k1_relat_1('#skF_11'(A_8917,B_8918)) != '#skF_13'
      | ~ r2_hidden(B_8918,'#skF_12')
      | k1_xboole_0 = A_8917 ) ),
    inference(resolution,[status(thm)],[c_72,c_10952])).

tff(c_10963,plain,(
    ! [A_53,B_57] :
      ( A_53 != '#skF_13'
      | ~ r2_hidden(B_57,'#skF_12')
      | k1_xboole_0 = A_53
      | k1_xboole_0 = A_53 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_10958])).

tff(c_10966,plain,(
    ! [B_8948] : ~ r2_hidden(B_8948,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_10963])).

tff(c_10996,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2364,c_10966])).

tff(c_11046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_10996])).

tff(c_11048,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_10963])).

tff(c_11233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11048,c_171])).

tff(c_11235,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_11234,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_11244,plain,(
    '#skF_13' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11235,c_11234])).

tff(c_11237,plain,(
    ! [A_11] : r1_tarski('#skF_13',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11234,c_14])).

tff(c_11262,plain,(
    ! [A_11] : r1_tarski('#skF_12',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11244,c_11237])).

tff(c_48,plain,(
    ! [A_37] :
      ( k2_relat_1(A_37) = k1_xboole_0
      | k1_relat_1(A_37) != k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_11353,plain,(
    ! [A_9007] :
      ( k2_relat_1(A_9007) = '#skF_12'
      | k1_relat_1(A_9007) != '#skF_12'
      | ~ v1_relat_1(A_9007) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11235,c_11235,c_48])).

tff(c_11362,plain,(
    ! [A_45] :
      ( k2_relat_1('#skF_10'(A_45)) = '#skF_12'
      | k1_relat_1('#skF_10'(A_45)) != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_64,c_11353])).

tff(c_11370,plain,(
    ! [A_9010] :
      ( k2_relat_1('#skF_10'(A_9010)) = '#skF_12'
      | A_9010 != '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11362])).

tff(c_11260,plain,(
    ! [C_60] :
      ( ~ r1_tarski(k2_relat_1(C_60),'#skF_12')
      | k1_relat_1(C_60) != '#skF_12'
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11244,c_76])).

tff(c_11379,plain,(
    ! [A_9010] :
      ( ~ r1_tarski('#skF_12','#skF_12')
      | k1_relat_1('#skF_10'(A_9010)) != '#skF_12'
      | ~ v1_funct_1('#skF_10'(A_9010))
      | ~ v1_relat_1('#skF_10'(A_9010))
      | A_9010 != '#skF_12' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11370,c_11260])).

tff(c_11386,plain,(
    ! [A_9010] : A_9010 != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_11262,c_11379])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11236,plain,(
    k2_relat_1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11234,c_11234,c_42])).

tff(c_11264,plain,(
    k2_relat_1('#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11244,c_11244,c_11236])).

tff(c_11402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11386,c_11264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.55/2.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.55/2.89  
% 8.55/2.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.55/2.89  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4
% 8.55/2.89  
% 8.55/2.89  %Foreground sorts:
% 8.55/2.89  
% 8.55/2.89  
% 8.55/2.89  %Background operators:
% 8.55/2.89  
% 8.55/2.89  
% 8.55/2.89  %Foreground operators:
% 8.55/2.89  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 8.55/2.89  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.55/2.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.55/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.55/2.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.55/2.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.55/2.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.55/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.55/2.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.55/2.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.55/2.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.55/2.89  tff('#skF_10', type, '#skF_10': $i > $i).
% 8.55/2.89  tff('#skF_13', type, '#skF_13': $i).
% 8.55/2.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.55/2.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.55/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.55/2.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.55/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.55/2.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.55/2.89  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 8.55/2.89  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.55/2.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.55/2.89  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.55/2.89  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.55/2.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.55/2.89  tff('#skF_12', type, '#skF_12': $i).
% 8.55/2.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.55/2.89  
% 8.78/2.91  tff(f_102, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 8.78/2.91  tff(f_141, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 8.78/2.91  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 8.78/2.91  tff(f_69, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 8.78/2.91  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.78/2.91  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.78/2.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.78/2.91  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.78/2.91  tff(f_123, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 8.78/2.91  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.78/2.91  tff(f_78, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 8.78/2.91  tff(c_64, plain, (![A_45]: (v1_relat_1('#skF_10'(A_45)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.78/2.91  tff(c_62, plain, (![A_45]: (v1_funct_1('#skF_10'(A_45)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.78/2.91  tff(c_60, plain, (![A_45]: (k1_relat_1('#skF_10'(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.78/2.91  tff(c_78, plain, (k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.78/2.91  tff(c_101, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_78])).
% 8.78/2.91  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.78/2.91  tff(c_2332, plain, (![A_3132, B_3133]: (r2_hidden(k4_tarski('#skF_5'(A_3132, B_3133), '#skF_6'(A_3132, B_3133)), A_3132) | r2_hidden('#skF_7'(A_3132, B_3133), B_3133) | k1_relat_1(A_3132)=B_3133)), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.78/2.91  tff(c_20, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.78/2.91  tff(c_260, plain, (![C_104, A_105, D_106]: (r2_hidden(C_104, k1_relat_1(A_105)) | ~r2_hidden(k4_tarski(C_104, D_106), A_105))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.78/2.91  tff(c_266, plain, (![C_107, D_108]: (r2_hidden(C_107, k1_relat_1(k1_tarski(k4_tarski(C_107, D_108)))))), inference(resolution, [status(thm)], [c_20, c_260])).
% 8.78/2.91  tff(c_32, plain, (![C_33, A_18, D_36]: (r2_hidden(C_33, k1_relat_1(A_18)) | ~r2_hidden(k4_tarski(C_33, D_36), A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.78/2.91  tff(c_271, plain, (![C_33, D_36, D_108]: (r2_hidden(C_33, k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(C_33, D_36), D_108))))))), inference(resolution, [status(thm)], [c_266, c_32])).
% 8.78/2.91  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.78/2.91  tff(c_272, plain, (![C_109, B_110, A_111]: (r2_hidden(C_109, B_110) | ~r2_hidden(C_109, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.78/2.91  tff(c_1051, plain, (![A_1730, B_1731, B_1732]: (r2_hidden('#skF_2'(A_1730, B_1731), B_1732) | ~r1_tarski(B_1731, B_1732) | r1_xboole_0(A_1730, B_1731))), inference(resolution, [status(thm)], [c_10, c_272])).
% 8.78/2.91  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.78/2.91  tff(c_296, plain, (![A_116, B_117, C_118]: (~r1_xboole_0(A_116, B_117) | ~r2_hidden(C_118, B_117) | ~r2_hidden(C_118, A_116))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.78/2.91  tff(c_299, plain, (![C_118, A_12]: (~r2_hidden(C_118, k1_xboole_0) | ~r2_hidden(C_118, A_12))), inference(resolution, [status(thm)], [c_16, c_296])).
% 8.78/2.91  tff(c_1311, plain, (![A_2107, B_2108, A_2109]: (~r2_hidden('#skF_2'(A_2107, B_2108), A_2109) | ~r1_tarski(B_2108, k1_xboole_0) | r1_xboole_0(A_2107, B_2108))), inference(resolution, [status(thm)], [c_1051, c_299])).
% 8.78/2.91  tff(c_1351, plain, (![B_2139, A_2140]: (~r1_tarski(B_2139, k1_xboole_0) | r1_xboole_0(A_2140, B_2139))), inference(resolution, [status(thm)], [c_271, c_1311])).
% 8.78/2.91  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.78/2.91  tff(c_1394, plain, (![C_2232, B_2233, A_2234]: (~r2_hidden(C_2232, B_2233) | ~r2_hidden(C_2232, A_2234) | ~r1_tarski(B_2233, k1_xboole_0))), inference(resolution, [status(thm)], [c_1351, c_8])).
% 8.78/2.91  tff(c_1434, plain, (![C_2264, A_2265]: (~r2_hidden(C_2264, A_2265) | ~r1_tarski(k1_tarski(C_2264), k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_1394])).
% 8.78/2.91  tff(c_1468, plain, (![C_33]: (~r1_tarski(k1_tarski(C_33), k1_xboole_0))), inference(resolution, [status(thm)], [c_271, c_1434])).
% 8.78/2.91  tff(c_197, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), A_89) | r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.78/2.91  tff(c_18, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.78/2.91  tff(c_202, plain, (![A_13, B_90]: ('#skF_1'(k1_tarski(A_13), B_90)=A_13 | r1_tarski(k1_tarski(A_13), B_90))), inference(resolution, [status(thm)], [c_197, c_18])).
% 8.78/2.91  tff(c_1511, plain, (![C_2326]: (~r1_tarski(k1_tarski(C_2326), k1_xboole_0))), inference(resolution, [status(thm)], [c_271, c_1434])).
% 8.78/2.91  tff(c_1526, plain, (![A_2387]: ('#skF_1'(k1_tarski(A_2387), k1_xboole_0)=A_2387)), inference(resolution, [status(thm)], [c_202, c_1511])).
% 8.78/2.91  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.78/2.91  tff(c_1538, plain, (![A_2387]: (~r2_hidden(A_2387, k1_xboole_0) | r1_tarski(k1_tarski(A_2387), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1526, c_4])).
% 8.78/2.91  tff(c_1601, plain, (![A_2387]: (~r2_hidden(A_2387, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1468, c_1538])).
% 8.78/2.91  tff(c_2347, plain, (![B_3133]: (r2_hidden('#skF_7'(k1_xboole_0, B_3133), B_3133) | k1_relat_1(k1_xboole_0)=B_3133)), inference(resolution, [status(thm)], [c_2332, c_1601])).
% 8.78/2.91  tff(c_2364, plain, (![B_3133]: (r2_hidden('#skF_7'(k1_xboole_0, B_3133), B_3133) | k1_xboole_0=B_3133)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2347])).
% 8.78/2.91  tff(c_70, plain, (![A_53, B_57]: (k1_relat_1('#skF_11'(A_53, B_57))=A_53 | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.91  tff(c_72, plain, (![A_53, B_57]: (v1_funct_1('#skF_11'(A_53, B_57)) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.91  tff(c_74, plain, (![A_53, B_57]: (v1_relat_1('#skF_11'(A_53, B_57)) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.91  tff(c_694, plain, (![A_1482, B_1483]: ('#skF_1'(k1_tarski(A_1482), B_1483)=A_1482 | r1_tarski(k1_tarski(A_1482), B_1483))), inference(resolution, [status(thm)], [c_197, c_18])).
% 8.78/2.91  tff(c_211, plain, (![A_94, B_95]: (k2_relat_1('#skF_11'(A_94, B_95))=k1_tarski(B_95) | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.91  tff(c_76, plain, (![C_60]: (~r1_tarski(k2_relat_1(C_60), '#skF_12') | k1_relat_1(C_60)!='#skF_13' | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.78/2.91  tff(c_217, plain, (![B_95, A_94]: (~r1_tarski(k1_tarski(B_95), '#skF_12') | k1_relat_1('#skF_11'(A_94, B_95))!='#skF_13' | ~v1_funct_1('#skF_11'(A_94, B_95)) | ~v1_relat_1('#skF_11'(A_94, B_95)) | k1_xboole_0=A_94)), inference(superposition, [status(thm), theory('equality')], [c_211, c_76])).
% 8.78/2.91  tff(c_1065, plain, (![A_1762, A_1763]: (k1_relat_1('#skF_11'(A_1762, A_1763))!='#skF_13' | ~v1_funct_1('#skF_11'(A_1762, A_1763)) | ~v1_relat_1('#skF_11'(A_1762, A_1763)) | k1_xboole_0=A_1762 | '#skF_1'(k1_tarski(A_1763), '#skF_12')=A_1763)), inference(resolution, [status(thm)], [c_694, c_217])).
% 8.78/2.91  tff(c_1369, plain, (![A_2201, B_2202]: (k1_relat_1('#skF_11'(A_2201, B_2202))!='#skF_13' | ~v1_funct_1('#skF_11'(A_2201, B_2202)) | '#skF_1'(k1_tarski(B_2202), '#skF_12')=B_2202 | k1_xboole_0=A_2201)), inference(resolution, [status(thm)], [c_74, c_1065])).
% 8.78/2.91  tff(c_5753, plain, (![A_5983, B_5984]: (k1_relat_1('#skF_11'(A_5983, B_5984))!='#skF_13' | '#skF_1'(k1_tarski(B_5984), '#skF_12')=B_5984 | k1_xboole_0=A_5983)), inference(resolution, [status(thm)], [c_72, c_1369])).
% 8.78/2.91  tff(c_5777, plain, (![A_53, B_57]: (A_53!='#skF_13' | '#skF_1'(k1_tarski(B_57), '#skF_12')=B_57 | k1_xboole_0=A_53 | k1_xboole_0=A_53)), inference(superposition, [status(thm), theory('equality')], [c_70, c_5753])).
% 8.78/2.91  tff(c_10276, plain, (k1_xboole_0='#skF_13'), inference(splitLeft, [status(thm)], [c_5777])).
% 8.78/2.91  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.78/2.91  tff(c_138, plain, (![A_82]: (k2_relat_1(A_82)=k1_xboole_0 | k1_relat_1(A_82)!=k1_xboole_0 | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.78/2.91  tff(c_147, plain, (![A_45]: (k2_relat_1('#skF_10'(A_45))=k1_xboole_0 | k1_relat_1('#skF_10'(A_45))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_138])).
% 8.78/2.91  tff(c_154, plain, (![A_83]: (k2_relat_1('#skF_10'(A_83))=k1_xboole_0 | k1_xboole_0!=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_147])).
% 8.78/2.91  tff(c_160, plain, (![A_83]: (~r1_tarski(k1_xboole_0, '#skF_12') | k1_relat_1('#skF_10'(A_83))!='#skF_13' | ~v1_funct_1('#skF_10'(A_83)) | ~v1_relat_1('#skF_10'(A_83)) | k1_xboole_0!=A_83)), inference(superposition, [status(thm), theory('equality')], [c_154, c_76])).
% 8.78/2.91  tff(c_166, plain, (![A_83]: (A_83!='#skF_13' | k1_xboole_0!=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_14, c_160])).
% 8.78/2.91  tff(c_171, plain, (k1_xboole_0!='#skF_13'), inference(reflexivity, [status(thm), theory('equality')], [c_166])).
% 8.78/2.91  tff(c_10459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10276, c_171])).
% 8.78/2.91  tff(c_10464, plain, (![B_8640]: ('#skF_1'(k1_tarski(B_8640), '#skF_12')=B_8640)), inference(splitRight, [status(thm)], [c_5777])).
% 8.78/2.91  tff(c_10545, plain, (![B_8670]: (~r2_hidden(B_8670, '#skF_12') | r1_tarski(k1_tarski(B_8670), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_10464, c_4])).
% 8.78/2.91  tff(c_10671, plain, (![A_8731, B_8732]: (k1_relat_1('#skF_11'(A_8731, B_8732))!='#skF_13' | ~v1_funct_1('#skF_11'(A_8731, B_8732)) | ~v1_relat_1('#skF_11'(A_8731, B_8732)) | k1_xboole_0=A_8731 | ~r2_hidden(B_8732, '#skF_12'))), inference(resolution, [status(thm)], [c_10545, c_217])).
% 8.78/2.91  tff(c_10952, plain, (![A_8886, B_8887]: (k1_relat_1('#skF_11'(A_8886, B_8887))!='#skF_13' | ~v1_funct_1('#skF_11'(A_8886, B_8887)) | ~r2_hidden(B_8887, '#skF_12') | k1_xboole_0=A_8886)), inference(resolution, [status(thm)], [c_74, c_10671])).
% 8.78/2.91  tff(c_10958, plain, (![A_8917, B_8918]: (k1_relat_1('#skF_11'(A_8917, B_8918))!='#skF_13' | ~r2_hidden(B_8918, '#skF_12') | k1_xboole_0=A_8917)), inference(resolution, [status(thm)], [c_72, c_10952])).
% 8.78/2.91  tff(c_10963, plain, (![A_53, B_57]: (A_53!='#skF_13' | ~r2_hidden(B_57, '#skF_12') | k1_xboole_0=A_53 | k1_xboole_0=A_53)), inference(superposition, [status(thm), theory('equality')], [c_70, c_10958])).
% 8.78/2.91  tff(c_10966, plain, (![B_8948]: (~r2_hidden(B_8948, '#skF_12'))), inference(splitLeft, [status(thm)], [c_10963])).
% 8.78/2.91  tff(c_10996, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_2364, c_10966])).
% 8.78/2.91  tff(c_11046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_10996])).
% 8.78/2.91  tff(c_11048, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_10963])).
% 8.78/2.91  tff(c_11233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11048, c_171])).
% 8.78/2.91  tff(c_11235, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_78])).
% 8.78/2.91  tff(c_11234, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_78])).
% 8.78/2.91  tff(c_11244, plain, ('#skF_13'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_11235, c_11234])).
% 8.78/2.91  tff(c_11237, plain, (![A_11]: (r1_tarski('#skF_13', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_11234, c_14])).
% 8.78/2.91  tff(c_11262, plain, (![A_11]: (r1_tarski('#skF_12', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_11244, c_11237])).
% 8.78/2.91  tff(c_48, plain, (![A_37]: (k2_relat_1(A_37)=k1_xboole_0 | k1_relat_1(A_37)!=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.78/2.91  tff(c_11353, plain, (![A_9007]: (k2_relat_1(A_9007)='#skF_12' | k1_relat_1(A_9007)!='#skF_12' | ~v1_relat_1(A_9007))), inference(demodulation, [status(thm), theory('equality')], [c_11235, c_11235, c_48])).
% 8.78/2.91  tff(c_11362, plain, (![A_45]: (k2_relat_1('#skF_10'(A_45))='#skF_12' | k1_relat_1('#skF_10'(A_45))!='#skF_12')), inference(resolution, [status(thm)], [c_64, c_11353])).
% 8.78/2.91  tff(c_11370, plain, (![A_9010]: (k2_relat_1('#skF_10'(A_9010))='#skF_12' | A_9010!='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11362])).
% 8.78/2.91  tff(c_11260, plain, (![C_60]: (~r1_tarski(k2_relat_1(C_60), '#skF_12') | k1_relat_1(C_60)!='#skF_12' | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(demodulation, [status(thm), theory('equality')], [c_11244, c_76])).
% 8.78/2.91  tff(c_11379, plain, (![A_9010]: (~r1_tarski('#skF_12', '#skF_12') | k1_relat_1('#skF_10'(A_9010))!='#skF_12' | ~v1_funct_1('#skF_10'(A_9010)) | ~v1_relat_1('#skF_10'(A_9010)) | A_9010!='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_11370, c_11260])).
% 8.78/2.91  tff(c_11386, plain, (![A_9010]: (A_9010!='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_11262, c_11379])).
% 8.78/2.91  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.78/2.91  tff(c_11236, plain, (k2_relat_1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_11234, c_11234, c_42])).
% 8.78/2.91  tff(c_11264, plain, (k2_relat_1('#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_11244, c_11244, c_11236])).
% 8.78/2.91  tff(c_11402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11386, c_11264])).
% 8.78/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/2.91  
% 8.78/2.91  Inference rules
% 8.78/2.91  ----------------------
% 8.78/2.91  #Ref     : 2
% 8.78/2.91  #Sup     : 2196
% 8.78/2.91  #Fact    : 2
% 8.78/2.91  #Define  : 0
% 8.78/2.91  #Split   : 9
% 8.78/2.91  #Chain   : 0
% 8.78/2.91  #Close   : 0
% 8.78/2.91  
% 8.78/2.91  Ordering : KBO
% 8.78/2.91  
% 8.78/2.91  Simplification rules
% 8.78/2.91  ----------------------
% 8.78/2.91  #Subsume      : 528
% 8.78/2.91  #Demod        : 1780
% 8.78/2.91  #Tautology    : 781
% 8.78/2.91  #SimpNegUnit  : 73
% 8.78/2.91  #BackRed      : 379
% 8.78/2.91  
% 8.78/2.91  #Partial instantiations: 5434
% 8.78/2.91  #Strategies tried      : 1
% 8.78/2.91  
% 8.78/2.91  Timing (in seconds)
% 8.78/2.91  ----------------------
% 8.78/2.92  Preprocessing        : 0.33
% 8.78/2.92  Parsing              : 0.17
% 8.78/2.92  CNF conversion       : 0.03
% 8.78/2.92  Main loop            : 1.79
% 8.78/2.92  Inferencing          : 0.61
% 8.78/2.92  Reduction            : 0.49
% 8.78/2.92  Demodulation         : 0.32
% 8.78/2.92  BG Simplification    : 0.06
% 8.78/2.92  Subsumption          : 0.49
% 8.78/2.92  Abstraction          : 0.08
% 8.78/2.92  MUC search           : 0.00
% 8.78/2.92  Cooper               : 0.00
% 8.78/2.92  Total                : 2.16
% 8.78/2.92  Index Insertion      : 0.00
% 8.78/2.92  Index Deletion       : 0.00
% 8.78/2.92  Index Matching       : 0.00
% 8.78/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
