%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:12 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 562 expanded)
%              Number of leaves         :   33 ( 188 expanded)
%              Depth                    :   15
%              Number of atoms          :  265 (1490 expanded)
%              Number of equality atoms :  104 ( 761 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_89,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
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

tff(f_102,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_9220,plain,(
    ! [A_2625,B_2626] :
      ( r2_hidden('#skF_1'(A_2625,B_2626),A_2625)
      | r1_tarski(A_2625,B_2626) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9229,plain,(
    ! [A_2625] : r1_tarski(A_2625,A_2625) ),
    inference(resolution,[status(thm)],[c_9220,c_4])).

tff(c_46,plain,(
    ! [A_21] : k1_relat_1('#skF_7'(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    ! [A_21] : v1_relat_1('#skF_7'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r2_hidden('#skF_3'(A_6,B_7),A_6)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_318,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_323,plain,(
    ! [A_15,B_82] :
      ( '#skF_1'(k1_tarski(A_15),B_82) = A_15
      | r1_tarski(k1_tarski(A_15),B_82) ) ),
    inference(resolution,[status(thm)],[c_318,c_24])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_354,plain,(
    ! [C_93,B_94,A_95] :
      ( r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_529,plain,(
    ! [A_132,B_133,B_134] :
      ( r2_hidden('#skF_1'(A_132,B_133),B_134)
      | ~ r1_tarski(A_132,B_134)
      | r1_tarski(A_132,B_133) ) ),
    inference(resolution,[status(thm)],[c_6,c_354])).

tff(c_22,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_350,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,B_91)
      | ~ r2_hidden(C_92,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_353,plain,(
    ! [C_92,A_14] :
      ( ~ r2_hidden(C_92,k1_xboole_0)
      | ~ r2_hidden(C_92,A_14) ) ),
    inference(resolution,[status(thm)],[c_22,c_350])).

tff(c_590,plain,(
    ! [A_143,B_144,A_145] :
      ( ~ r2_hidden('#skF_1'(A_143,B_144),A_145)
      | ~ r1_tarski(A_143,k1_xboole_0)
      | r1_tarski(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_529,c_353])).

tff(c_606,plain,(
    ! [A_146,B_147] :
      ( ~ r1_tarski(A_146,k1_xboole_0)
      | r1_tarski(A_146,B_147) ) ),
    inference(resolution,[status(thm)],[c_6,c_590])).

tff(c_628,plain,(
    ! [A_150,B_151] :
      ( r1_tarski(k1_tarski(A_150),B_151)
      | '#skF_1'(k1_tarski(A_150),k1_xboole_0) = A_150 ) ),
    inference(resolution,[status(thm)],[c_323,c_606])).

tff(c_26,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_366,plain,(
    ! [C_19,B_94] :
      ( r2_hidden(C_19,B_94)
      | ~ r1_tarski(k1_tarski(C_19),B_94) ) ),
    inference(resolution,[status(thm)],[c_26,c_354])).

tff(c_645,plain,(
    ! [A_152,B_153] :
      ( r2_hidden(A_152,B_153)
      | '#skF_1'(k1_tarski(A_152),k1_xboole_0) = A_152 ) ),
    inference(resolution,[status(thm)],[c_628,c_366])).

tff(c_695,plain,(
    ! [A_152,A_15] :
      ( A_152 = A_15
      | '#skF_1'(k1_tarski(A_152),k1_xboole_0) = A_152 ) ),
    inference(resolution,[status(thm)],[c_645,c_24])).

tff(c_7143,plain,(
    ! [A_2475] : '#skF_1'(k1_tarski(A_2475),k1_xboole_0) = A_2475 ),
    inference(factorization,[status(thm),theory(equality)],[c_695])).

tff(c_7198,plain,(
    ! [A_2478] :
      ( ~ r2_hidden(A_2478,k1_xboole_0)
      | r1_tarski(k1_tarski(A_2478),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7143,c_4])).

tff(c_604,plain,(
    ! [A_1,B_2] :
      ( ~ r1_tarski(A_1,k1_xboole_0)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_590])).

tff(c_7204,plain,(
    ! [A_2478,B_2] :
      ( r1_tarski(k1_tarski(A_2478),B_2)
      | ~ r2_hidden(A_2478,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7198,c_604])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_4'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_559,plain,(
    ! [A_137,B_138,B_139] :
      ( r2_hidden('#skF_4'(A_137,B_138),B_139)
      | ~ r1_tarski(A_137,B_139)
      | r1_xboole_0(A_137,B_138) ) ),
    inference(resolution,[status(thm)],[c_20,c_354])).

tff(c_7452,plain,(
    ! [A_2503,B_2504,A_2505] :
      ( ~ r2_hidden('#skF_4'(A_2503,B_2504),A_2505)
      | ~ r1_tarski(A_2503,k1_xboole_0)
      | r1_xboole_0(A_2503,B_2504) ) ),
    inference(resolution,[status(thm)],[c_559,c_353])).

tff(c_7473,plain,(
    ! [A_2506,B_2507] :
      ( ~ r1_tarski(A_2506,k1_xboole_0)
      | r1_xboole_0(A_2506,B_2507) ) ),
    inference(resolution,[status(thm)],[c_20,c_7452])).

tff(c_16,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,B_10)
      | ~ r2_hidden(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7501,plain,(
    ! [C_2510,B_2511,A_2512] :
      ( ~ r2_hidden(C_2510,B_2511)
      | ~ r2_hidden(C_2510,A_2512)
      | ~ r1_tarski(A_2512,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7473,c_16])).

tff(c_7544,plain,(
    ! [C_2513,A_2514] :
      ( ~ r2_hidden(C_2513,A_2514)
      | ~ r1_tarski(A_2514,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_7501])).

tff(c_7601,plain,(
    ! [C_2515] : ~ r1_tarski(k1_tarski(C_2515),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_7544])).

tff(c_7612,plain,(
    ! [A_2516] : ~ r2_hidden(A_2516,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7204,c_7601])).

tff(c_7666,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_7),B_7)
      | k1_xboole_0 = B_7 ) ),
    inference(resolution,[status(thm)],[c_14,c_7612])).

tff(c_54,plain,(
    ! [A_27,B_31] :
      ( k1_relat_1('#skF_8'(A_27,B_31)) = A_27
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,(
    ! [A_27,B_31] :
      ( v1_funct_1('#skF_8'(A_27,B_31))
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_58,plain,(
    ! [A_27,B_31] :
      ( v1_relat_1('#skF_8'(A_27,B_31))
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_447,plain,(
    ! [A_116,B_117] :
      ( '#skF_1'(k1_tarski(A_116),B_117) = A_116
      | r1_tarski(k1_tarski(A_116),B_117) ) ),
    inference(resolution,[status(thm)],[c_318,c_24])).

tff(c_325,plain,(
    ! [A_83,B_84] :
      ( k2_relat_1('#skF_8'(A_83,B_84)) = k1_tarski(B_84)
      | k1_xboole_0 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_60,plain,(
    ! [C_34] :
      ( ~ r1_tarski(k2_relat_1(C_34),'#skF_9')
      | k1_relat_1(C_34) != '#skF_10'
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_331,plain,(
    ! [B_84,A_83] :
      ( ~ r1_tarski(k1_tarski(B_84),'#skF_9')
      | k1_relat_1('#skF_8'(A_83,B_84)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_83,B_84))
      | ~ v1_relat_1('#skF_8'(A_83,B_84))
      | k1_xboole_0 = A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_60])).

tff(c_554,plain,(
    ! [A_135,A_136] :
      ( k1_relat_1('#skF_8'(A_135,A_136)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_135,A_136))
      | ~ v1_relat_1('#skF_8'(A_135,A_136))
      | k1_xboole_0 = A_135
      | '#skF_1'(k1_tarski(A_136),'#skF_9') = A_136 ) ),
    inference(resolution,[status(thm)],[c_447,c_331])).

tff(c_7937,plain,(
    ! [A_2531,B_2532] :
      ( k1_relat_1('#skF_8'(A_2531,B_2532)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_2531,B_2532))
      | '#skF_1'(k1_tarski(B_2532),'#skF_9') = B_2532
      | k1_xboole_0 = A_2531 ) ),
    inference(resolution,[status(thm)],[c_58,c_554])).

tff(c_8664,plain,(
    ! [A_2588,B_2589] :
      ( k1_relat_1('#skF_8'(A_2588,B_2589)) != '#skF_10'
      | '#skF_1'(k1_tarski(B_2589),'#skF_9') = B_2589
      | k1_xboole_0 = A_2588 ) ),
    inference(resolution,[status(thm)],[c_56,c_7937])).

tff(c_8667,plain,(
    ! [A_27,B_31] :
      ( A_27 != '#skF_10'
      | '#skF_1'(k1_tarski(B_31),'#skF_9') = B_31
      | k1_xboole_0 = A_27
      | k1_xboole_0 = A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8664])).

tff(c_8669,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_8667])).

tff(c_243,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,B_67)
      | ~ r2_hidden(C_68,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_247,plain,(
    ! [C_69,A_70] :
      ( ~ r2_hidden(C_69,k1_xboole_0)
      | ~ r2_hidden(C_69,A_70) ) ),
    inference(resolution,[status(thm)],[c_22,c_243])).

tff(c_284,plain,(
    ! [B_76,A_77] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_76),A_77)
      | r1_tarski(k1_xboole_0,B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_247])).

tff(c_292,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_108,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) != k1_xboole_0
      | k1_xboole_0 = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_114,plain,(
    ! [A_21] :
      ( k1_relat_1('#skF_7'(A_21)) != k1_xboole_0
      | '#skF_7'(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_128,plain,(
    ! [A_51] :
      ( k1_xboole_0 != A_51
      | '#skF_7'(A_51) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_114])).

tff(c_48,plain,(
    ! [A_21] : v1_funct_1('#skF_7'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_136,plain,(
    ! [A_51] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_48])).

tff(c_145,plain,(
    ! [A_51] : k1_xboole_0 != A_51 ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_36])).

tff(c_155,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_85,plain,(
    ! [C_40] :
      ( ~ r1_tarski(k2_relat_1(C_40),'#skF_9')
      | k1_relat_1(C_40) != '#skF_10'
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_88,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_9')
    | k1_relat_1(k1_xboole_0) != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_85])).

tff(c_89,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_9')
    | k1_xboole_0 != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_88])).

tff(c_156,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_138,plain,(
    ! [A_51] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_50])).

tff(c_157,plain,(
    ! [A_51] : k1_xboole_0 != A_51 ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_138])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_36])).

tff(c_167,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_10'
    | ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_191,plain,
    ( k1_xboole_0 != '#skF_10'
    | ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_167])).

tff(c_192,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_192])).

tff(c_298,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_8724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8669,c_298])).

tff(c_8727,plain,(
    ! [B_2590] : '#skF_1'(k1_tarski(B_2590),'#skF_9') = B_2590 ),
    inference(splitRight,[status(thm)],[c_8667])).

tff(c_8758,plain,(
    ! [B_2591] :
      ( ~ r2_hidden(B_2591,'#skF_9')
      | r1_tarski(k1_tarski(B_2591),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8727,c_4])).

tff(c_8877,plain,(
    ! [A_2597,B_2598] :
      ( k1_relat_1('#skF_8'(A_2597,B_2598)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_2597,B_2598))
      | ~ v1_relat_1('#skF_8'(A_2597,B_2598))
      | k1_xboole_0 = A_2597
      | ~ r2_hidden(B_2598,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_8758,c_331])).

tff(c_8891,plain,(
    ! [A_2599,B_2600] :
      ( k1_relat_1('#skF_8'(A_2599,B_2600)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_2599,B_2600))
      | ~ r2_hidden(B_2600,'#skF_9')
      | k1_xboole_0 = A_2599 ) ),
    inference(resolution,[status(thm)],[c_58,c_8877])).

tff(c_8896,plain,(
    ! [A_2601,B_2602] :
      ( k1_relat_1('#skF_8'(A_2601,B_2602)) != '#skF_10'
      | ~ r2_hidden(B_2602,'#skF_9')
      | k1_xboole_0 = A_2601 ) ),
    inference(resolution,[status(thm)],[c_56,c_8891])).

tff(c_8899,plain,(
    ! [A_27,B_31] :
      ( A_27 != '#skF_10'
      | ~ r2_hidden(B_31,'#skF_9')
      | k1_xboole_0 = A_27
      | k1_xboole_0 = A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8896])).

tff(c_8901,plain,(
    ! [B_2603] : ~ r2_hidden(B_2603,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_8899])).

tff(c_8933,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7666,c_8901])).

tff(c_8997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_8933])).

tff(c_8999,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_8899])).

tff(c_9054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8999,c_298])).

tff(c_9056,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_42,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9102,plain,(
    ! [A_2613] :
      ( k1_relat_1(A_2613) != '#skF_9'
      | A_2613 = '#skF_9'
      | ~ v1_relat_1(A_2613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9056,c_9056,c_42])).

tff(c_9108,plain,(
    ! [A_21] :
      ( k1_relat_1('#skF_7'(A_21)) != '#skF_9'
      | '#skF_7'(A_21) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_50,c_9102])).

tff(c_9113,plain,(
    ! [A_2614] :
      ( A_2614 != '#skF_9'
      | '#skF_7'(A_2614) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_9108])).

tff(c_9121,plain,(
    ! [A_2614] :
      ( v1_funct_1('#skF_9')
      | A_2614 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9113,c_48])).

tff(c_9130,plain,(
    ! [A_2614] : A_2614 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_9121])).

tff(c_9055,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_9064,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9056,c_9055])).

tff(c_9058,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9055,c_9055,c_38])).

tff(c_9085,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9064,c_9064,c_9058])).

tff(c_9139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9130,c_9085])).

tff(c_9140,plain,(
    v1_funct_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_9121])).

tff(c_9057,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9055,c_9055,c_36])).

tff(c_9075,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9064,c_9064,c_9057])).

tff(c_9081,plain,(
    ! [C_2605] :
      ( ~ r1_tarski(k2_relat_1(C_2605),'#skF_9')
      | k1_relat_1(C_2605) != '#skF_9'
      | ~ v1_funct_1(C_2605)
      | ~ v1_relat_1(C_2605) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9064,c_60])).

tff(c_9084,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | k1_relat_1('#skF_9') != '#skF_9'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_9075,c_9081])).

tff(c_9142,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9085,c_9084])).

tff(c_9143,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_9142])).

tff(c_9123,plain,(
    ! [A_2614] :
      ( v1_relat_1('#skF_9')
      | A_2614 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9113,c_50])).

tff(c_9144,plain,(
    ! [A_2614] : A_2614 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_9143,c_9123])).

tff(c_9153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9144,c_9085])).

tff(c_9154,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(splitRight,[status(thm)],[c_9142])).

tff(c_9176,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9140,c_9154])).

tff(c_9233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9229,c_9176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.22  
% 5.71/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 5.71/2.22  
% 5.71/2.22  %Foreground sorts:
% 5.71/2.22  
% 5.71/2.22  
% 5.71/2.22  %Background operators:
% 5.71/2.22  
% 5.71/2.22  
% 5.71/2.22  %Foreground operators:
% 5.71/2.22  tff('#skF_7', type, '#skF_7': $i > $i).
% 5.71/2.22  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.71/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.71/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.71/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.71/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.71/2.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.71/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.71/2.22  tff('#skF_10', type, '#skF_10': $i).
% 5.71/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.71/2.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.71/2.22  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.71/2.22  tff('#skF_9', type, '#skF_9': $i).
% 5.71/2.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.71/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.71/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.71/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.71/2.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.71/2.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.71/2.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.71/2.22  
% 5.71/2.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.71/2.24  tff(f_89, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 5.71/2.24  tff(f_120, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 5.71/2.24  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.71/2.24  tff(f_66, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.71/2.24  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.71/2.24  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.71/2.24  tff(f_102, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 5.71/2.24  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.71/2.24  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.71/2.24  tff(c_9220, plain, (![A_2625, B_2626]: (r2_hidden('#skF_1'(A_2625, B_2626), A_2625) | r1_tarski(A_2625, B_2626))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.71/2.24  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.71/2.24  tff(c_9229, plain, (![A_2625]: (r1_tarski(A_2625, A_2625))), inference(resolution, [status(thm)], [c_9220, c_4])).
% 5.71/2.24  tff(c_46, plain, (![A_21]: (k1_relat_1('#skF_7'(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.71/2.24  tff(c_50, plain, (![A_21]: (v1_relat_1('#skF_7'(A_21)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.71/2.24  tff(c_62, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.71/2.24  tff(c_83, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_62])).
% 5.71/2.24  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r2_hidden('#skF_3'(A_6, B_7), A_6) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.71/2.24  tff(c_318, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.71/2.24  tff(c_24, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.71/2.24  tff(c_323, plain, (![A_15, B_82]: ('#skF_1'(k1_tarski(A_15), B_82)=A_15 | r1_tarski(k1_tarski(A_15), B_82))), inference(resolution, [status(thm)], [c_318, c_24])).
% 5.71/2.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.71/2.24  tff(c_354, plain, (![C_93, B_94, A_95]: (r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.71/2.24  tff(c_529, plain, (![A_132, B_133, B_134]: (r2_hidden('#skF_1'(A_132, B_133), B_134) | ~r1_tarski(A_132, B_134) | r1_tarski(A_132, B_133))), inference(resolution, [status(thm)], [c_6, c_354])).
% 5.71/2.24  tff(c_22, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.71/2.24  tff(c_350, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, B_91) | ~r2_hidden(C_92, A_90))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.71/2.24  tff(c_353, plain, (![C_92, A_14]: (~r2_hidden(C_92, k1_xboole_0) | ~r2_hidden(C_92, A_14))), inference(resolution, [status(thm)], [c_22, c_350])).
% 5.71/2.24  tff(c_590, plain, (![A_143, B_144, A_145]: (~r2_hidden('#skF_1'(A_143, B_144), A_145) | ~r1_tarski(A_143, k1_xboole_0) | r1_tarski(A_143, B_144))), inference(resolution, [status(thm)], [c_529, c_353])).
% 5.71/2.24  tff(c_606, plain, (![A_146, B_147]: (~r1_tarski(A_146, k1_xboole_0) | r1_tarski(A_146, B_147))), inference(resolution, [status(thm)], [c_6, c_590])).
% 5.71/2.24  tff(c_628, plain, (![A_150, B_151]: (r1_tarski(k1_tarski(A_150), B_151) | '#skF_1'(k1_tarski(A_150), k1_xboole_0)=A_150)), inference(resolution, [status(thm)], [c_323, c_606])).
% 5.71/2.24  tff(c_26, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.71/2.24  tff(c_366, plain, (![C_19, B_94]: (r2_hidden(C_19, B_94) | ~r1_tarski(k1_tarski(C_19), B_94))), inference(resolution, [status(thm)], [c_26, c_354])).
% 5.71/2.24  tff(c_645, plain, (![A_152, B_153]: (r2_hidden(A_152, B_153) | '#skF_1'(k1_tarski(A_152), k1_xboole_0)=A_152)), inference(resolution, [status(thm)], [c_628, c_366])).
% 5.71/2.24  tff(c_695, plain, (![A_152, A_15]: (A_152=A_15 | '#skF_1'(k1_tarski(A_152), k1_xboole_0)=A_152)), inference(resolution, [status(thm)], [c_645, c_24])).
% 5.71/2.24  tff(c_7143, plain, (![A_2475]: ('#skF_1'(k1_tarski(A_2475), k1_xboole_0)=A_2475)), inference(factorization, [status(thm), theory('equality')], [c_695])).
% 5.71/2.24  tff(c_7198, plain, (![A_2478]: (~r2_hidden(A_2478, k1_xboole_0) | r1_tarski(k1_tarski(A_2478), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7143, c_4])).
% 5.71/2.24  tff(c_604, plain, (![A_1, B_2]: (~r1_tarski(A_1, k1_xboole_0) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_590])).
% 5.71/2.24  tff(c_7204, plain, (![A_2478, B_2]: (r1_tarski(k1_tarski(A_2478), B_2) | ~r2_hidden(A_2478, k1_xboole_0))), inference(resolution, [status(thm)], [c_7198, c_604])).
% 5.71/2.24  tff(c_20, plain, (![A_9, B_10]: (r2_hidden('#skF_4'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.71/2.24  tff(c_559, plain, (![A_137, B_138, B_139]: (r2_hidden('#skF_4'(A_137, B_138), B_139) | ~r1_tarski(A_137, B_139) | r1_xboole_0(A_137, B_138))), inference(resolution, [status(thm)], [c_20, c_354])).
% 5.71/2.24  tff(c_7452, plain, (![A_2503, B_2504, A_2505]: (~r2_hidden('#skF_4'(A_2503, B_2504), A_2505) | ~r1_tarski(A_2503, k1_xboole_0) | r1_xboole_0(A_2503, B_2504))), inference(resolution, [status(thm)], [c_559, c_353])).
% 5.71/2.24  tff(c_7473, plain, (![A_2506, B_2507]: (~r1_tarski(A_2506, k1_xboole_0) | r1_xboole_0(A_2506, B_2507))), inference(resolution, [status(thm)], [c_20, c_7452])).
% 5.71/2.24  tff(c_16, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, B_10) | ~r2_hidden(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.71/2.24  tff(c_7501, plain, (![C_2510, B_2511, A_2512]: (~r2_hidden(C_2510, B_2511) | ~r2_hidden(C_2510, A_2512) | ~r1_tarski(A_2512, k1_xboole_0))), inference(resolution, [status(thm)], [c_7473, c_16])).
% 5.71/2.24  tff(c_7544, plain, (![C_2513, A_2514]: (~r2_hidden(C_2513, A_2514) | ~r1_tarski(A_2514, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_7501])).
% 5.71/2.24  tff(c_7601, plain, (![C_2515]: (~r1_tarski(k1_tarski(C_2515), k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_7544])).
% 5.71/2.24  tff(c_7612, plain, (![A_2516]: (~r2_hidden(A_2516, k1_xboole_0))), inference(resolution, [status(thm)], [c_7204, c_7601])).
% 5.71/2.24  tff(c_7666, plain, (![B_7]: (r2_hidden('#skF_2'(k1_xboole_0, B_7), B_7) | k1_xboole_0=B_7)), inference(resolution, [status(thm)], [c_14, c_7612])).
% 5.71/2.24  tff(c_54, plain, (![A_27, B_31]: (k1_relat_1('#skF_8'(A_27, B_31))=A_27 | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.71/2.24  tff(c_56, plain, (![A_27, B_31]: (v1_funct_1('#skF_8'(A_27, B_31)) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.71/2.24  tff(c_58, plain, (![A_27, B_31]: (v1_relat_1('#skF_8'(A_27, B_31)) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.71/2.24  tff(c_447, plain, (![A_116, B_117]: ('#skF_1'(k1_tarski(A_116), B_117)=A_116 | r1_tarski(k1_tarski(A_116), B_117))), inference(resolution, [status(thm)], [c_318, c_24])).
% 5.71/2.24  tff(c_325, plain, (![A_83, B_84]: (k2_relat_1('#skF_8'(A_83, B_84))=k1_tarski(B_84) | k1_xboole_0=A_83)), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.71/2.24  tff(c_60, plain, (![C_34]: (~r1_tarski(k2_relat_1(C_34), '#skF_9') | k1_relat_1(C_34)!='#skF_10' | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.71/2.24  tff(c_331, plain, (![B_84, A_83]: (~r1_tarski(k1_tarski(B_84), '#skF_9') | k1_relat_1('#skF_8'(A_83, B_84))!='#skF_10' | ~v1_funct_1('#skF_8'(A_83, B_84)) | ~v1_relat_1('#skF_8'(A_83, B_84)) | k1_xboole_0=A_83)), inference(superposition, [status(thm), theory('equality')], [c_325, c_60])).
% 5.71/2.24  tff(c_554, plain, (![A_135, A_136]: (k1_relat_1('#skF_8'(A_135, A_136))!='#skF_10' | ~v1_funct_1('#skF_8'(A_135, A_136)) | ~v1_relat_1('#skF_8'(A_135, A_136)) | k1_xboole_0=A_135 | '#skF_1'(k1_tarski(A_136), '#skF_9')=A_136)), inference(resolution, [status(thm)], [c_447, c_331])).
% 5.71/2.24  tff(c_7937, plain, (![A_2531, B_2532]: (k1_relat_1('#skF_8'(A_2531, B_2532))!='#skF_10' | ~v1_funct_1('#skF_8'(A_2531, B_2532)) | '#skF_1'(k1_tarski(B_2532), '#skF_9')=B_2532 | k1_xboole_0=A_2531)), inference(resolution, [status(thm)], [c_58, c_554])).
% 5.71/2.24  tff(c_8664, plain, (![A_2588, B_2589]: (k1_relat_1('#skF_8'(A_2588, B_2589))!='#skF_10' | '#skF_1'(k1_tarski(B_2589), '#skF_9')=B_2589 | k1_xboole_0=A_2588)), inference(resolution, [status(thm)], [c_56, c_7937])).
% 5.71/2.24  tff(c_8667, plain, (![A_27, B_31]: (A_27!='#skF_10' | '#skF_1'(k1_tarski(B_31), '#skF_9')=B_31 | k1_xboole_0=A_27 | k1_xboole_0=A_27)), inference(superposition, [status(thm), theory('equality')], [c_54, c_8664])).
% 5.71/2.24  tff(c_8669, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_8667])).
% 5.71/2.24  tff(c_243, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, B_67) | ~r2_hidden(C_68, A_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.71/2.24  tff(c_247, plain, (![C_69, A_70]: (~r2_hidden(C_69, k1_xboole_0) | ~r2_hidden(C_69, A_70))), inference(resolution, [status(thm)], [c_22, c_243])).
% 5.71/2.24  tff(c_284, plain, (![B_76, A_77]: (~r2_hidden('#skF_1'(k1_xboole_0, B_76), A_77) | r1_tarski(k1_xboole_0, B_76))), inference(resolution, [status(thm)], [c_6, c_247])).
% 5.71/2.24  tff(c_292, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_284])).
% 5.71/2.24  tff(c_108, plain, (![A_49]: (k1_relat_1(A_49)!=k1_xboole_0 | k1_xboole_0=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.71/2.24  tff(c_114, plain, (![A_21]: (k1_relat_1('#skF_7'(A_21))!=k1_xboole_0 | '#skF_7'(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_108])).
% 5.71/2.24  tff(c_128, plain, (![A_51]: (k1_xboole_0!=A_51 | '#skF_7'(A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_114])).
% 5.71/2.24  tff(c_48, plain, (![A_21]: (v1_funct_1('#skF_7'(A_21)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.71/2.24  tff(c_136, plain, (![A_51]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_51)), inference(superposition, [status(thm), theory('equality')], [c_128, c_48])).
% 5.71/2.24  tff(c_145, plain, (![A_51]: (k1_xboole_0!=A_51)), inference(splitLeft, [status(thm)], [c_136])).
% 5.71/2.24  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.24  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_36])).
% 5.71/2.24  tff(c_155, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_136])).
% 5.71/2.24  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.24  tff(c_85, plain, (![C_40]: (~r1_tarski(k2_relat_1(C_40), '#skF_9') | k1_relat_1(C_40)!='#skF_10' | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.71/2.24  tff(c_88, plain, (~r1_tarski(k1_xboole_0, '#skF_9') | k1_relat_1(k1_xboole_0)!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_85])).
% 5.71/2.24  tff(c_89, plain, (~r1_tarski(k1_xboole_0, '#skF_9') | k1_xboole_0!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_88])).
% 5.71/2.24  tff(c_156, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_89])).
% 5.71/2.24  tff(c_138, plain, (![A_51]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_51)), inference(superposition, [status(thm), theory('equality')], [c_128, c_50])).
% 5.71/2.24  tff(c_157, plain, (![A_51]: (k1_xboole_0!=A_51)), inference(negUnitSimplification, [status(thm)], [c_156, c_138])).
% 5.71/2.24  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_36])).
% 5.71/2.24  tff(c_167, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_10' | ~r1_tarski(k1_xboole_0, '#skF_9')), inference(splitRight, [status(thm)], [c_89])).
% 5.71/2.24  tff(c_191, plain, (k1_xboole_0!='#skF_10' | ~r1_tarski(k1_xboole_0, '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_167])).
% 5.71/2.24  tff(c_192, plain, (~r1_tarski(k1_xboole_0, '#skF_9')), inference(splitLeft, [status(thm)], [c_191])).
% 5.71/2.24  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_292, c_192])).
% 5.71/2.24  tff(c_298, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_191])).
% 5.71/2.24  tff(c_8724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8669, c_298])).
% 5.71/2.24  tff(c_8727, plain, (![B_2590]: ('#skF_1'(k1_tarski(B_2590), '#skF_9')=B_2590)), inference(splitRight, [status(thm)], [c_8667])).
% 5.71/2.24  tff(c_8758, plain, (![B_2591]: (~r2_hidden(B_2591, '#skF_9') | r1_tarski(k1_tarski(B_2591), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_8727, c_4])).
% 5.71/2.24  tff(c_8877, plain, (![A_2597, B_2598]: (k1_relat_1('#skF_8'(A_2597, B_2598))!='#skF_10' | ~v1_funct_1('#skF_8'(A_2597, B_2598)) | ~v1_relat_1('#skF_8'(A_2597, B_2598)) | k1_xboole_0=A_2597 | ~r2_hidden(B_2598, '#skF_9'))), inference(resolution, [status(thm)], [c_8758, c_331])).
% 5.71/2.24  tff(c_8891, plain, (![A_2599, B_2600]: (k1_relat_1('#skF_8'(A_2599, B_2600))!='#skF_10' | ~v1_funct_1('#skF_8'(A_2599, B_2600)) | ~r2_hidden(B_2600, '#skF_9') | k1_xboole_0=A_2599)), inference(resolution, [status(thm)], [c_58, c_8877])).
% 5.71/2.24  tff(c_8896, plain, (![A_2601, B_2602]: (k1_relat_1('#skF_8'(A_2601, B_2602))!='#skF_10' | ~r2_hidden(B_2602, '#skF_9') | k1_xboole_0=A_2601)), inference(resolution, [status(thm)], [c_56, c_8891])).
% 5.71/2.24  tff(c_8899, plain, (![A_27, B_31]: (A_27!='#skF_10' | ~r2_hidden(B_31, '#skF_9') | k1_xboole_0=A_27 | k1_xboole_0=A_27)), inference(superposition, [status(thm), theory('equality')], [c_54, c_8896])).
% 5.71/2.24  tff(c_8901, plain, (![B_2603]: (~r2_hidden(B_2603, '#skF_9'))), inference(splitLeft, [status(thm)], [c_8899])).
% 5.71/2.24  tff(c_8933, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_7666, c_8901])).
% 5.71/2.24  tff(c_8997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_8933])).
% 5.71/2.24  tff(c_8999, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_8899])).
% 5.71/2.24  tff(c_9054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8999, c_298])).
% 5.71/2.24  tff(c_9056, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_62])).
% 5.71/2.24  tff(c_42, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.71/2.24  tff(c_9102, plain, (![A_2613]: (k1_relat_1(A_2613)!='#skF_9' | A_2613='#skF_9' | ~v1_relat_1(A_2613))), inference(demodulation, [status(thm), theory('equality')], [c_9056, c_9056, c_42])).
% 5.71/2.24  tff(c_9108, plain, (![A_21]: (k1_relat_1('#skF_7'(A_21))!='#skF_9' | '#skF_7'(A_21)='#skF_9')), inference(resolution, [status(thm)], [c_50, c_9102])).
% 5.71/2.24  tff(c_9113, plain, (![A_2614]: (A_2614!='#skF_9' | '#skF_7'(A_2614)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_9108])).
% 5.71/2.24  tff(c_9121, plain, (![A_2614]: (v1_funct_1('#skF_9') | A_2614!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_9113, c_48])).
% 5.71/2.24  tff(c_9130, plain, (![A_2614]: (A_2614!='#skF_9')), inference(splitLeft, [status(thm)], [c_9121])).
% 5.71/2.24  tff(c_9055, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_62])).
% 5.71/2.24  tff(c_9064, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9056, c_9055])).
% 5.71/2.24  tff(c_9058, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_9055, c_9055, c_38])).
% 5.71/2.24  tff(c_9085, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9064, c_9064, c_9058])).
% 5.71/2.24  tff(c_9139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9130, c_9085])).
% 5.71/2.24  tff(c_9140, plain, (v1_funct_1('#skF_9')), inference(splitRight, [status(thm)], [c_9121])).
% 5.71/2.24  tff(c_9057, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_9055, c_9055, c_36])).
% 5.71/2.24  tff(c_9075, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9064, c_9064, c_9057])).
% 5.71/2.24  tff(c_9081, plain, (![C_2605]: (~r1_tarski(k2_relat_1(C_2605), '#skF_9') | k1_relat_1(C_2605)!='#skF_9' | ~v1_funct_1(C_2605) | ~v1_relat_1(C_2605))), inference(demodulation, [status(thm), theory('equality')], [c_9064, c_60])).
% 5.71/2.24  tff(c_9084, plain, (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_9')!='#skF_9' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_9075, c_9081])).
% 5.71/2.24  tff(c_9142, plain, (~r1_tarski('#skF_9', '#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9085, c_9084])).
% 5.71/2.24  tff(c_9143, plain, (~v1_relat_1('#skF_9')), inference(splitLeft, [status(thm)], [c_9142])).
% 5.71/2.24  tff(c_9123, plain, (![A_2614]: (v1_relat_1('#skF_9') | A_2614!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_9113, c_50])).
% 5.71/2.24  tff(c_9144, plain, (![A_2614]: (A_2614!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_9143, c_9123])).
% 5.71/2.24  tff(c_9153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9144, c_9085])).
% 5.71/2.24  tff(c_9154, plain, (~v1_funct_1('#skF_9') | ~r1_tarski('#skF_9', '#skF_9')), inference(splitRight, [status(thm)], [c_9142])).
% 5.71/2.24  tff(c_9176, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9140, c_9154])).
% 5.71/2.24  tff(c_9233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9229, c_9176])).
% 5.71/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.24  
% 5.71/2.24  Inference rules
% 5.71/2.24  ----------------------
% 5.71/2.24  #Ref     : 0
% 5.71/2.24  #Sup     : 1543
% 5.71/2.24  #Fact    : 2
% 5.71/2.24  #Define  : 0
% 5.71/2.24  #Split   : 8
% 5.71/2.24  #Chain   : 0
% 5.71/2.24  #Close   : 0
% 5.71/2.24  
% 5.71/2.24  Ordering : KBO
% 5.71/2.24  
% 5.71/2.24  Simplification rules
% 5.71/2.24  ----------------------
% 5.71/2.24  #Subsume      : 428
% 5.71/2.24  #Demod        : 486
% 5.71/2.24  #Tautology    : 306
% 5.71/2.24  #SimpNegUnit  : 48
% 5.71/2.24  #BackRed      : 134
% 5.71/2.24  
% 5.71/2.24  #Partial instantiations: 1710
% 5.71/2.24  #Strategies tried      : 1
% 5.71/2.24  
% 5.71/2.24  Timing (in seconds)
% 5.71/2.24  ----------------------
% 5.71/2.24  Preprocessing        : 0.32
% 5.71/2.25  Parsing              : 0.15
% 5.71/2.25  CNF conversion       : 0.03
% 5.71/2.25  Main loop            : 1.04
% 5.71/2.25  Inferencing          : 0.38
% 5.71/2.25  Reduction            : 0.29
% 5.71/2.25  Demodulation         : 0.20
% 5.71/2.25  BG Simplification    : 0.05
% 5.71/2.25  Subsumption          : 0.23
% 5.71/2.25  Abstraction          : 0.06
% 5.71/2.25  MUC search           : 0.00
% 5.71/2.25  Cooper               : 0.00
% 5.71/2.25  Total                : 1.40
% 5.71/2.25  Index Insertion      : 0.00
% 5.71/2.25  Index Deletion       : 0.00
% 5.71/2.25  Index Matching       : 0.00
% 5.71/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
