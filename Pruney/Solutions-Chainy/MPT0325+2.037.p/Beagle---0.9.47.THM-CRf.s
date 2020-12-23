%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:25 EST 2020

% Result     : Theorem 6.46s
% Output     : CNFRefutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 380 expanded)
%              Number of leaves         :   34 ( 137 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 ( 881 expanded)
%              Number of equality atoms :   56 ( 145 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

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

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_11','#skF_13')
    | ~ r1_tarski('#skF_10','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_88,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_88])).

tff(c_106,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_103])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_154,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,B_78)
      | ~ r2_hidden(C_79,A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_197,plain,(
    ! [C_95,B_96,A_97] :
      ( ~ r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,A_97)
      | k4_xboole_0(A_97,B_96) != A_97 ) ),
    inference(resolution,[status(thm)],[c_24,c_154])).

tff(c_325,plain,(
    ! [A_120,B_121,A_122] :
      ( ~ r2_hidden('#skF_2'(A_120,B_121),A_122)
      | k4_xboole_0(A_122,B_121) != A_122
      | r1_xboole_0(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_10,c_197])).

tff(c_337,plain,(
    ! [B_7,A_6] :
      ( k4_xboole_0(B_7,B_7) != B_7
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_325])).

tff(c_351,plain,(
    ! [B_126,A_127] :
      ( k1_xboole_0 != B_126
      | r1_xboole_0(A_127,B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_337])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_439,plain,(
    ! [C_135,B_136,A_137] :
      ( ~ r2_hidden(C_135,B_136)
      | ~ r2_hidden(C_135,A_137)
      | k1_xboole_0 != B_136 ) ),
    inference(resolution,[status(thm)],[c_351,c_8])).

tff(c_725,plain,(
    ! [A_162,B_163,A_164] :
      ( ~ r2_hidden('#skF_1'(A_162,B_163),A_164)
      | k1_xboole_0 != A_162
      | r1_tarski(A_162,B_163) ) ),
    inference(resolution,[status(thm)],[c_6,c_439])).

tff(c_735,plain,(
    ! [A_165,B_166] :
      ( k1_xboole_0 != A_165
      | r1_tarski(A_165,B_166) ) ),
    inference(resolution,[status(thm)],[c_6,c_725])).

tff(c_746,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(resolution,[status(thm)],[c_735,c_78])).

tff(c_60,plain,(
    r1_tarski(k2_zfmisc_1('#skF_10','#skF_11'),k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_214,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( r2_hidden(k4_tarski(A_98,B_99),k2_zfmisc_1(C_100,D_101))
      | ~ r2_hidden(B_99,D_101)
      | ~ r2_hidden(A_98,C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1098,plain,(
    ! [C_215,A_217,D_216,B_214,B_218] :
      ( r2_hidden(k4_tarski(A_217,B_214),B_218)
      | ~ r1_tarski(k2_zfmisc_1(C_215,D_216),B_218)
      | ~ r2_hidden(B_214,D_216)
      | ~ r2_hidden(A_217,C_215) ) ),
    inference(resolution,[status(thm)],[c_214,c_2])).

tff(c_1183,plain,(
    ! [A_221,B_222] :
      ( r2_hidden(k4_tarski(A_221,B_222),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_222,'#skF_11')
      | ~ r2_hidden(A_221,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_60,c_1098])).

tff(c_52,plain,(
    ! [B_54,D_56,A_53,C_55] :
      ( r2_hidden(B_54,D_56)
      | ~ r2_hidden(k4_tarski(A_53,B_54),k2_zfmisc_1(C_55,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1207,plain,(
    ! [B_222,A_221] :
      ( r2_hidden(B_222,'#skF_13')
      | ~ r2_hidden(B_222,'#skF_11')
      | ~ r2_hidden(A_221,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1183,c_52])).

tff(c_1211,plain,(
    ! [A_223] : ~ r2_hidden(A_223,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1207])).

tff(c_1263,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_14,c_1211])).

tff(c_1278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_1263])).

tff(c_1280,plain,(
    ! [B_224] :
      ( r2_hidden(B_224,'#skF_13')
      | ~ r2_hidden(B_224,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_1207])).

tff(c_1344,plain,
    ( r2_hidden('#skF_3'('#skF_11'),'#skF_13')
    | k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_14,c_1280])).

tff(c_1345,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_1344])).

tff(c_2064,plain,(
    ! [A_280] :
      ( r2_hidden('#skF_3'(A_280),A_280)
      | A_280 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_14])).

tff(c_30,plain,(
    ! [A_19,B_20,D_46] :
      ( r2_hidden('#skF_9'(A_19,B_20,k2_zfmisc_1(A_19,B_20),D_46),B_20)
      | ~ r2_hidden(D_46,k2_zfmisc_1(A_19,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_54,plain,(
    ! [A_53,C_55,B_54,D_56] :
      ( r2_hidden(A_53,C_55)
      | ~ r2_hidden(k4_tarski(A_53,B_54),k2_zfmisc_1(C_55,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1208,plain,(
    ! [A_221,B_222] :
      ( r2_hidden(A_221,'#skF_12')
      | ~ r2_hidden(B_222,'#skF_11')
      | ~ r2_hidden(A_221,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1183,c_54])).

tff(c_1406,plain,(
    ! [B_230] : ~ r2_hidden(B_230,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1208])).

tff(c_1462,plain,(
    ! [D_46,A_19] : ~ r2_hidden(D_46,k2_zfmisc_1(A_19,'#skF_11')) ),
    inference(resolution,[status(thm)],[c_30,c_1406])).

tff(c_2082,plain,(
    ! [A_19] : k2_zfmisc_1(A_19,'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_2064,c_1462])).

tff(c_58,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1371,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_58])).

tff(c_2250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2082,c_1371])).

tff(c_2348,plain,(
    ! [A_298] :
      ( r2_hidden(A_298,'#skF_12')
      | ~ r2_hidden(A_298,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_1208])).

tff(c_2874,plain,(
    ! [B_332] :
      ( r2_hidden('#skF_1'('#skF_10',B_332),'#skF_12')
      | r1_tarski('#skF_10',B_332) ) ),
    inference(resolution,[status(thm)],[c_6,c_2348])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2882,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_2874,c_4])).

tff(c_2888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_2882])).

tff(c_2890,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_1344])).

tff(c_2942,plain,(
    ! [B_337] : ~ r2_hidden(B_337,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1208])).

tff(c_2998,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_14,c_2942])).

tff(c_3014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2890,c_2998])).

tff(c_3016,plain,(
    ! [A_338] :
      ( r2_hidden(A_338,'#skF_12')
      | ~ r2_hidden(A_338,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_1208])).

tff(c_3659,plain,(
    ! [B_381] :
      ( r2_hidden('#skF_1'('#skF_10',B_381),'#skF_12')
      | r1_tarski('#skF_10',B_381) ) ),
    inference(resolution,[status(thm)],[c_6,c_3016])).

tff(c_3671,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_3659,c_4])).

tff(c_3679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_3671])).

tff(c_3680,plain,(
    ~ r1_tarski('#skF_11','#skF_13') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3690,plain,(
    ! [A_390,B_391] : k4_xboole_0(A_390,k4_xboole_0(A_390,B_391)) = k3_xboole_0(A_390,B_391) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3705,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3690])).

tff(c_3708,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3705])).

tff(c_3757,plain,(
    ! [A_399,B_400,C_401] :
      ( ~ r1_xboole_0(A_399,B_400)
      | ~ r2_hidden(C_401,B_400)
      | ~ r2_hidden(C_401,A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3801,plain,(
    ! [C_417,B_418,A_419] :
      ( ~ r2_hidden(C_417,B_418)
      | ~ r2_hidden(C_417,A_419)
      | k4_xboole_0(A_419,B_418) != A_419 ) ),
    inference(resolution,[status(thm)],[c_24,c_3757])).

tff(c_4064,plain,(
    ! [A_468,B_469,A_470] :
      ( ~ r2_hidden('#skF_2'(A_468,B_469),A_470)
      | k4_xboole_0(A_470,B_469) != A_470
      | r1_xboole_0(A_468,B_469) ) ),
    inference(resolution,[status(thm)],[c_10,c_3801])).

tff(c_4076,plain,(
    ! [B_7,A_6] :
      ( k4_xboole_0(B_7,B_7) != B_7
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_4064])).

tff(c_4083,plain,(
    ! [B_471,A_472] :
      ( k1_xboole_0 != B_471
      | r1_xboole_0(A_472,B_471) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3708,c_4076])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4093,plain,(
    ! [A_473,B_474] :
      ( k4_xboole_0(A_473,B_474) = A_473
      | k1_xboole_0 != B_474 ) ),
    inference(resolution,[status(thm)],[c_4083,c_22])).

tff(c_3681,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3761,plain,(
    ! [C_402,B_403,A_404] :
      ( r2_hidden(C_402,B_403)
      | ~ r2_hidden(C_402,A_404)
      | ~ r1_tarski(A_404,B_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3773,plain,(
    ! [A_11,B_403] :
      ( r2_hidden('#skF_3'(A_11),B_403)
      | ~ r1_tarski(A_11,B_403)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_3761])).

tff(c_3832,plain,(
    ! [A_424,A_425] :
      ( ~ r2_hidden('#skF_3'(A_424),A_425)
      | k4_xboole_0(A_425,A_424) != A_425
      | k1_xboole_0 = A_424 ) ),
    inference(resolution,[status(thm)],[c_14,c_3801])).

tff(c_3842,plain,(
    ! [B_426,A_427] :
      ( k4_xboole_0(B_426,A_427) != B_426
      | ~ r1_tarski(A_427,B_426)
      | k1_xboole_0 = A_427 ) ),
    inference(resolution,[status(thm)],[c_3773,c_3832])).

tff(c_3854,plain,
    ( k4_xboole_0('#skF_12','#skF_10') != '#skF_12'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_3681,c_3842])).

tff(c_3858,plain,(
    k4_xboole_0('#skF_12','#skF_10') != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_3854])).

tff(c_4143,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_4093,c_3858])).

tff(c_3817,plain,(
    ! [A_420,B_421,C_422,D_423] :
      ( r2_hidden(k4_tarski(A_420,B_421),k2_zfmisc_1(C_422,D_423))
      | ~ r2_hidden(B_421,D_423)
      | ~ r2_hidden(A_420,C_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5524,plain,(
    ! [C_584,B_587,A_588,D_585,B_586] :
      ( r2_hidden(k4_tarski(A_588,B_586),B_587)
      | ~ r1_tarski(k2_zfmisc_1(C_584,D_585),B_587)
      | ~ r2_hidden(B_586,D_585)
      | ~ r2_hidden(A_588,C_584) ) ),
    inference(resolution,[status(thm)],[c_3817,c_2])).

tff(c_5549,plain,(
    ! [A_590,B_591] :
      ( r2_hidden(k4_tarski(A_590,B_591),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_591,'#skF_11')
      | ~ r2_hidden(A_590,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_60,c_5524])).

tff(c_5573,plain,(
    ! [B_591,A_590] :
      ( r2_hidden(B_591,'#skF_13')
      | ~ r2_hidden(B_591,'#skF_11')
      | ~ r2_hidden(A_590,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_5549,c_52])).

tff(c_5577,plain,(
    ! [A_592] : ~ r2_hidden(A_592,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_5573])).

tff(c_5637,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_14,c_5577])).

tff(c_5654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4143,c_5637])).

tff(c_5656,plain,(
    ! [B_593] :
      ( r2_hidden(B_593,'#skF_13')
      | ~ r2_hidden(B_593,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_5573])).

tff(c_6518,plain,(
    ! [B_632] :
      ( r2_hidden('#skF_1'('#skF_11',B_632),'#skF_13')
      | r1_tarski('#skF_11',B_632) ) ),
    inference(resolution,[status(thm)],[c_6,c_5656])).

tff(c_6536,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_6518,c_4])).

tff(c_6546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3680,c_3680,c_6536])).

tff(c_6547,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_3854])).

tff(c_6553,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6547,c_14])).

tff(c_32,plain,(
    ! [A_19,B_20,D_46] :
      ( r2_hidden('#skF_8'(A_19,B_20,k2_zfmisc_1(A_19,B_20),D_46),A_19)
      | ~ r2_hidden(D_46,k2_zfmisc_1(A_19,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7645,plain,(
    ! [A_765,B_763,C_761,D_762,B_764] :
      ( r2_hidden(k4_tarski(A_765,B_763),B_764)
      | ~ r1_tarski(k2_zfmisc_1(C_761,D_762),B_764)
      | ~ r2_hidden(B_763,D_762)
      | ~ r2_hidden(A_765,C_761) ) ),
    inference(resolution,[status(thm)],[c_3817,c_2])).

tff(c_7761,plain,(
    ! [A_768,B_769] :
      ( r2_hidden(k4_tarski(A_768,B_769),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_769,'#skF_11')
      | ~ r2_hidden(A_768,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_60,c_7645])).

tff(c_7785,plain,(
    ! [B_769,A_768] :
      ( r2_hidden(B_769,'#skF_13')
      | ~ r2_hidden(B_769,'#skF_11')
      | ~ r2_hidden(A_768,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_7761,c_52])).

tff(c_7789,plain,(
    ! [A_770] : ~ r2_hidden(A_770,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_7785])).

tff(c_7974,plain,(
    ! [D_774,B_775] : ~ r2_hidden(D_774,k2_zfmisc_1('#skF_10',B_775)) ),
    inference(resolution,[status(thm)],[c_32,c_7789])).

tff(c_8047,plain,(
    ! [B_775] : k2_zfmisc_1('#skF_10',B_775) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6553,c_7974])).

tff(c_6556,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6547,c_58])).

tff(c_8086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8047,c_6556])).

tff(c_8088,plain,(
    ! [B_780] :
      ( r2_hidden(B_780,'#skF_13')
      | ~ r2_hidden(B_780,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_7785])).

tff(c_8483,plain,(
    ! [B_799] :
      ( r2_hidden('#skF_1'('#skF_11',B_799),'#skF_13')
      | r1_tarski('#skF_11',B_799) ) ),
    inference(resolution,[status(thm)],[c_6,c_8088])).

tff(c_8495,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_8483,c_4])).

tff(c_8503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3680,c_3680,c_8495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:24:34 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.46/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.46/2.39  
% 6.46/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.46/2.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 6.46/2.39  
% 6.46/2.39  %Foreground sorts:
% 6.46/2.39  
% 6.46/2.39  
% 6.46/2.39  %Background operators:
% 6.46/2.39  
% 6.46/2.39  
% 6.46/2.39  %Foreground operators:
% 6.46/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.46/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.46/2.39  tff('#skF_11', type, '#skF_11': $i).
% 6.46/2.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.46/2.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.46/2.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.46/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.46/2.39  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 6.46/2.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.46/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.46/2.39  tff('#skF_10', type, '#skF_10': $i).
% 6.46/2.39  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 6.46/2.39  tff('#skF_13', type, '#skF_13': $i).
% 6.46/2.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.46/2.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.46/2.39  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.46/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.46/2.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.46/2.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.46/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.46/2.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.46/2.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.46/2.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.46/2.39  tff('#skF_12', type, '#skF_12': $i).
% 6.46/2.39  
% 6.46/2.41  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 6.46/2.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.46/2.41  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.46/2.41  tff(f_60, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.46/2.41  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.46/2.41  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.46/2.41  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.46/2.41  tff(f_68, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.46/2.41  tff(f_86, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.46/2.41  tff(f_80, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.46/2.41  tff(c_56, plain, (~r1_tarski('#skF_11', '#skF_13') | ~r1_tarski('#skF_10', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.46/2.41  tff(c_78, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitLeft, [status(thm)], [c_56])).
% 6.46/2.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.46/2.41  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.46/2.41  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.46/2.41  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.46/2.41  tff(c_88, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.46/2.41  tff(c_103, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_88])).
% 6.46/2.41  tff(c_106, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_103])).
% 6.46/2.41  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.46/2.41  tff(c_24, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.46/2.41  tff(c_154, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, B_78) | ~r2_hidden(C_79, A_77))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.46/2.41  tff(c_197, plain, (![C_95, B_96, A_97]: (~r2_hidden(C_95, B_96) | ~r2_hidden(C_95, A_97) | k4_xboole_0(A_97, B_96)!=A_97)), inference(resolution, [status(thm)], [c_24, c_154])).
% 6.46/2.41  tff(c_325, plain, (![A_120, B_121, A_122]: (~r2_hidden('#skF_2'(A_120, B_121), A_122) | k4_xboole_0(A_122, B_121)!=A_122 | r1_xboole_0(A_120, B_121))), inference(resolution, [status(thm)], [c_10, c_197])).
% 6.46/2.41  tff(c_337, plain, (![B_7, A_6]: (k4_xboole_0(B_7, B_7)!=B_7 | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_325])).
% 6.46/2.41  tff(c_351, plain, (![B_126, A_127]: (k1_xboole_0!=B_126 | r1_xboole_0(A_127, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_337])).
% 6.46/2.41  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.46/2.41  tff(c_439, plain, (![C_135, B_136, A_137]: (~r2_hidden(C_135, B_136) | ~r2_hidden(C_135, A_137) | k1_xboole_0!=B_136)), inference(resolution, [status(thm)], [c_351, c_8])).
% 6.46/2.41  tff(c_725, plain, (![A_162, B_163, A_164]: (~r2_hidden('#skF_1'(A_162, B_163), A_164) | k1_xboole_0!=A_162 | r1_tarski(A_162, B_163))), inference(resolution, [status(thm)], [c_6, c_439])).
% 6.46/2.41  tff(c_735, plain, (![A_165, B_166]: (k1_xboole_0!=A_165 | r1_tarski(A_165, B_166))), inference(resolution, [status(thm)], [c_6, c_725])).
% 6.46/2.41  tff(c_746, plain, (k1_xboole_0!='#skF_10'), inference(resolution, [status(thm)], [c_735, c_78])).
% 6.46/2.41  tff(c_60, plain, (r1_tarski(k2_zfmisc_1('#skF_10', '#skF_11'), k2_zfmisc_1('#skF_12', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.46/2.41  tff(c_214, plain, (![A_98, B_99, C_100, D_101]: (r2_hidden(k4_tarski(A_98, B_99), k2_zfmisc_1(C_100, D_101)) | ~r2_hidden(B_99, D_101) | ~r2_hidden(A_98, C_100))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.46/2.41  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.46/2.41  tff(c_1098, plain, (![C_215, A_217, D_216, B_214, B_218]: (r2_hidden(k4_tarski(A_217, B_214), B_218) | ~r1_tarski(k2_zfmisc_1(C_215, D_216), B_218) | ~r2_hidden(B_214, D_216) | ~r2_hidden(A_217, C_215))), inference(resolution, [status(thm)], [c_214, c_2])).
% 6.46/2.41  tff(c_1183, plain, (![A_221, B_222]: (r2_hidden(k4_tarski(A_221, B_222), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_222, '#skF_11') | ~r2_hidden(A_221, '#skF_10'))), inference(resolution, [status(thm)], [c_60, c_1098])).
% 6.46/2.41  tff(c_52, plain, (![B_54, D_56, A_53, C_55]: (r2_hidden(B_54, D_56) | ~r2_hidden(k4_tarski(A_53, B_54), k2_zfmisc_1(C_55, D_56)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.46/2.41  tff(c_1207, plain, (![B_222, A_221]: (r2_hidden(B_222, '#skF_13') | ~r2_hidden(B_222, '#skF_11') | ~r2_hidden(A_221, '#skF_10'))), inference(resolution, [status(thm)], [c_1183, c_52])).
% 6.46/2.41  tff(c_1211, plain, (![A_223]: (~r2_hidden(A_223, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1207])).
% 6.46/2.41  tff(c_1263, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_14, c_1211])).
% 6.46/2.41  tff(c_1278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_746, c_1263])).
% 6.46/2.41  tff(c_1280, plain, (![B_224]: (r2_hidden(B_224, '#skF_13') | ~r2_hidden(B_224, '#skF_11'))), inference(splitRight, [status(thm)], [c_1207])).
% 6.46/2.41  tff(c_1344, plain, (r2_hidden('#skF_3'('#skF_11'), '#skF_13') | k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_14, c_1280])).
% 6.46/2.41  tff(c_1345, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_1344])).
% 6.46/2.41  tff(c_2064, plain, (![A_280]: (r2_hidden('#skF_3'(A_280), A_280) | A_280='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_14])).
% 6.46/2.41  tff(c_30, plain, (![A_19, B_20, D_46]: (r2_hidden('#skF_9'(A_19, B_20, k2_zfmisc_1(A_19, B_20), D_46), B_20) | ~r2_hidden(D_46, k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.46/2.41  tff(c_54, plain, (![A_53, C_55, B_54, D_56]: (r2_hidden(A_53, C_55) | ~r2_hidden(k4_tarski(A_53, B_54), k2_zfmisc_1(C_55, D_56)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.46/2.41  tff(c_1208, plain, (![A_221, B_222]: (r2_hidden(A_221, '#skF_12') | ~r2_hidden(B_222, '#skF_11') | ~r2_hidden(A_221, '#skF_10'))), inference(resolution, [status(thm)], [c_1183, c_54])).
% 6.46/2.41  tff(c_1406, plain, (![B_230]: (~r2_hidden(B_230, '#skF_11'))), inference(splitLeft, [status(thm)], [c_1208])).
% 6.46/2.41  tff(c_1462, plain, (![D_46, A_19]: (~r2_hidden(D_46, k2_zfmisc_1(A_19, '#skF_11')))), inference(resolution, [status(thm)], [c_30, c_1406])).
% 6.46/2.41  tff(c_2082, plain, (![A_19]: (k2_zfmisc_1(A_19, '#skF_11')='#skF_11')), inference(resolution, [status(thm)], [c_2064, c_1462])).
% 6.46/2.41  tff(c_58, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.46/2.41  tff(c_1371, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_58])).
% 6.46/2.41  tff(c_2250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2082, c_1371])).
% 6.46/2.41  tff(c_2348, plain, (![A_298]: (r2_hidden(A_298, '#skF_12') | ~r2_hidden(A_298, '#skF_10'))), inference(splitRight, [status(thm)], [c_1208])).
% 6.46/2.41  tff(c_2874, plain, (![B_332]: (r2_hidden('#skF_1'('#skF_10', B_332), '#skF_12') | r1_tarski('#skF_10', B_332))), inference(resolution, [status(thm)], [c_6, c_2348])).
% 6.46/2.41  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.46/2.41  tff(c_2882, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_2874, c_4])).
% 6.46/2.41  tff(c_2888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_78, c_2882])).
% 6.46/2.41  tff(c_2890, plain, (k1_xboole_0!='#skF_11'), inference(splitRight, [status(thm)], [c_1344])).
% 6.46/2.41  tff(c_2942, plain, (![B_337]: (~r2_hidden(B_337, '#skF_11'))), inference(splitLeft, [status(thm)], [c_1208])).
% 6.46/2.41  tff(c_2998, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_14, c_2942])).
% 6.46/2.41  tff(c_3014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2890, c_2998])).
% 6.46/2.41  tff(c_3016, plain, (![A_338]: (r2_hidden(A_338, '#skF_12') | ~r2_hidden(A_338, '#skF_10'))), inference(splitRight, [status(thm)], [c_1208])).
% 6.46/2.41  tff(c_3659, plain, (![B_381]: (r2_hidden('#skF_1'('#skF_10', B_381), '#skF_12') | r1_tarski('#skF_10', B_381))), inference(resolution, [status(thm)], [c_6, c_3016])).
% 6.46/2.41  tff(c_3671, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_3659, c_4])).
% 6.46/2.41  tff(c_3679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_78, c_3671])).
% 6.46/2.41  tff(c_3680, plain, (~r1_tarski('#skF_11', '#skF_13')), inference(splitRight, [status(thm)], [c_56])).
% 6.46/2.41  tff(c_3690, plain, (![A_390, B_391]: (k4_xboole_0(A_390, k4_xboole_0(A_390, B_391))=k3_xboole_0(A_390, B_391))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.46/2.41  tff(c_3705, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3690])).
% 6.46/2.41  tff(c_3708, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3705])).
% 6.46/2.41  tff(c_3757, plain, (![A_399, B_400, C_401]: (~r1_xboole_0(A_399, B_400) | ~r2_hidden(C_401, B_400) | ~r2_hidden(C_401, A_399))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.46/2.41  tff(c_3801, plain, (![C_417, B_418, A_419]: (~r2_hidden(C_417, B_418) | ~r2_hidden(C_417, A_419) | k4_xboole_0(A_419, B_418)!=A_419)), inference(resolution, [status(thm)], [c_24, c_3757])).
% 6.46/2.41  tff(c_4064, plain, (![A_468, B_469, A_470]: (~r2_hidden('#skF_2'(A_468, B_469), A_470) | k4_xboole_0(A_470, B_469)!=A_470 | r1_xboole_0(A_468, B_469))), inference(resolution, [status(thm)], [c_10, c_3801])).
% 6.46/2.41  tff(c_4076, plain, (![B_7, A_6]: (k4_xboole_0(B_7, B_7)!=B_7 | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_4064])).
% 6.46/2.41  tff(c_4083, plain, (![B_471, A_472]: (k1_xboole_0!=B_471 | r1_xboole_0(A_472, B_471))), inference(demodulation, [status(thm), theory('equality')], [c_3708, c_4076])).
% 6.46/2.41  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.46/2.41  tff(c_4093, plain, (![A_473, B_474]: (k4_xboole_0(A_473, B_474)=A_473 | k1_xboole_0!=B_474)), inference(resolution, [status(thm)], [c_4083, c_22])).
% 6.46/2.41  tff(c_3681, plain, (r1_tarski('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_56])).
% 6.46/2.41  tff(c_3761, plain, (![C_402, B_403, A_404]: (r2_hidden(C_402, B_403) | ~r2_hidden(C_402, A_404) | ~r1_tarski(A_404, B_403))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.46/2.41  tff(c_3773, plain, (![A_11, B_403]: (r2_hidden('#skF_3'(A_11), B_403) | ~r1_tarski(A_11, B_403) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_3761])).
% 6.46/2.41  tff(c_3832, plain, (![A_424, A_425]: (~r2_hidden('#skF_3'(A_424), A_425) | k4_xboole_0(A_425, A_424)!=A_425 | k1_xboole_0=A_424)), inference(resolution, [status(thm)], [c_14, c_3801])).
% 6.46/2.41  tff(c_3842, plain, (![B_426, A_427]: (k4_xboole_0(B_426, A_427)!=B_426 | ~r1_tarski(A_427, B_426) | k1_xboole_0=A_427)), inference(resolution, [status(thm)], [c_3773, c_3832])).
% 6.46/2.41  tff(c_3854, plain, (k4_xboole_0('#skF_12', '#skF_10')!='#skF_12' | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_3681, c_3842])).
% 6.46/2.41  tff(c_3858, plain, (k4_xboole_0('#skF_12', '#skF_10')!='#skF_12'), inference(splitLeft, [status(thm)], [c_3854])).
% 6.46/2.41  tff(c_4143, plain, (k1_xboole_0!='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_4093, c_3858])).
% 6.46/2.41  tff(c_3817, plain, (![A_420, B_421, C_422, D_423]: (r2_hidden(k4_tarski(A_420, B_421), k2_zfmisc_1(C_422, D_423)) | ~r2_hidden(B_421, D_423) | ~r2_hidden(A_420, C_422))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.46/2.41  tff(c_5524, plain, (![C_584, B_587, A_588, D_585, B_586]: (r2_hidden(k4_tarski(A_588, B_586), B_587) | ~r1_tarski(k2_zfmisc_1(C_584, D_585), B_587) | ~r2_hidden(B_586, D_585) | ~r2_hidden(A_588, C_584))), inference(resolution, [status(thm)], [c_3817, c_2])).
% 6.46/2.41  tff(c_5549, plain, (![A_590, B_591]: (r2_hidden(k4_tarski(A_590, B_591), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_591, '#skF_11') | ~r2_hidden(A_590, '#skF_10'))), inference(resolution, [status(thm)], [c_60, c_5524])).
% 6.46/2.41  tff(c_5573, plain, (![B_591, A_590]: (r2_hidden(B_591, '#skF_13') | ~r2_hidden(B_591, '#skF_11') | ~r2_hidden(A_590, '#skF_10'))), inference(resolution, [status(thm)], [c_5549, c_52])).
% 6.46/2.41  tff(c_5577, plain, (![A_592]: (~r2_hidden(A_592, '#skF_10'))), inference(splitLeft, [status(thm)], [c_5573])).
% 6.46/2.41  tff(c_5637, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_14, c_5577])).
% 6.46/2.41  tff(c_5654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4143, c_5637])).
% 6.46/2.41  tff(c_5656, plain, (![B_593]: (r2_hidden(B_593, '#skF_13') | ~r2_hidden(B_593, '#skF_11'))), inference(splitRight, [status(thm)], [c_5573])).
% 6.46/2.41  tff(c_6518, plain, (![B_632]: (r2_hidden('#skF_1'('#skF_11', B_632), '#skF_13') | r1_tarski('#skF_11', B_632))), inference(resolution, [status(thm)], [c_6, c_5656])).
% 6.46/2.41  tff(c_6536, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_6518, c_4])).
% 6.46/2.41  tff(c_6546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3680, c_3680, c_6536])).
% 6.46/2.41  tff(c_6547, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_3854])).
% 6.46/2.41  tff(c_6553, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_6547, c_14])).
% 6.46/2.41  tff(c_32, plain, (![A_19, B_20, D_46]: (r2_hidden('#skF_8'(A_19, B_20, k2_zfmisc_1(A_19, B_20), D_46), A_19) | ~r2_hidden(D_46, k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.46/2.41  tff(c_7645, plain, (![A_765, B_763, C_761, D_762, B_764]: (r2_hidden(k4_tarski(A_765, B_763), B_764) | ~r1_tarski(k2_zfmisc_1(C_761, D_762), B_764) | ~r2_hidden(B_763, D_762) | ~r2_hidden(A_765, C_761))), inference(resolution, [status(thm)], [c_3817, c_2])).
% 6.46/2.41  tff(c_7761, plain, (![A_768, B_769]: (r2_hidden(k4_tarski(A_768, B_769), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_769, '#skF_11') | ~r2_hidden(A_768, '#skF_10'))), inference(resolution, [status(thm)], [c_60, c_7645])).
% 6.46/2.41  tff(c_7785, plain, (![B_769, A_768]: (r2_hidden(B_769, '#skF_13') | ~r2_hidden(B_769, '#skF_11') | ~r2_hidden(A_768, '#skF_10'))), inference(resolution, [status(thm)], [c_7761, c_52])).
% 6.46/2.41  tff(c_7789, plain, (![A_770]: (~r2_hidden(A_770, '#skF_10'))), inference(splitLeft, [status(thm)], [c_7785])).
% 6.46/2.41  tff(c_7974, plain, (![D_774, B_775]: (~r2_hidden(D_774, k2_zfmisc_1('#skF_10', B_775)))), inference(resolution, [status(thm)], [c_32, c_7789])).
% 6.46/2.41  tff(c_8047, plain, (![B_775]: (k2_zfmisc_1('#skF_10', B_775)='#skF_10')), inference(resolution, [status(thm)], [c_6553, c_7974])).
% 6.46/2.41  tff(c_6556, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6547, c_58])).
% 6.46/2.41  tff(c_8086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8047, c_6556])).
% 6.46/2.41  tff(c_8088, plain, (![B_780]: (r2_hidden(B_780, '#skF_13') | ~r2_hidden(B_780, '#skF_11'))), inference(splitRight, [status(thm)], [c_7785])).
% 6.46/2.41  tff(c_8483, plain, (![B_799]: (r2_hidden('#skF_1'('#skF_11', B_799), '#skF_13') | r1_tarski('#skF_11', B_799))), inference(resolution, [status(thm)], [c_6, c_8088])).
% 6.46/2.41  tff(c_8495, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_8483, c_4])).
% 6.46/2.41  tff(c_8503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3680, c_3680, c_8495])).
% 6.46/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.46/2.41  
% 6.46/2.41  Inference rules
% 6.46/2.41  ----------------------
% 6.46/2.41  #Ref     : 0
% 6.46/2.41  #Sup     : 1996
% 6.46/2.41  #Fact    : 0
% 6.46/2.41  #Define  : 0
% 6.46/2.41  #Split   : 20
% 6.46/2.41  #Chain   : 0
% 6.46/2.41  #Close   : 0
% 6.46/2.41  
% 6.46/2.41  Ordering : KBO
% 6.46/2.41  
% 6.46/2.41  Simplification rules
% 6.46/2.41  ----------------------
% 6.46/2.41  #Subsume      : 408
% 6.46/2.41  #Demod        : 475
% 6.46/2.41  #Tautology    : 593
% 6.46/2.41  #SimpNegUnit  : 80
% 6.46/2.41  #BackRed      : 49
% 6.46/2.41  
% 6.46/2.41  #Partial instantiations: 0
% 6.46/2.41  #Strategies tried      : 1
% 6.46/2.41  
% 6.46/2.41  Timing (in seconds)
% 6.46/2.41  ----------------------
% 6.46/2.42  Preprocessing        : 0.32
% 6.46/2.42  Parsing              : 0.17
% 6.46/2.42  CNF conversion       : 0.03
% 6.46/2.42  Main loop            : 1.31
% 6.46/2.42  Inferencing          : 0.47
% 6.46/2.42  Reduction            : 0.37
% 6.46/2.42  Demodulation         : 0.25
% 6.46/2.42  BG Simplification    : 0.06
% 6.46/2.42  Subsumption          : 0.29
% 6.46/2.42  Abstraction          : 0.07
% 6.46/2.42  MUC search           : 0.00
% 6.46/2.42  Cooper               : 0.00
% 6.46/2.42  Total                : 1.68
% 6.46/2.42  Index Insertion      : 0.00
% 6.46/2.42  Index Deletion       : 0.00
% 6.46/2.42  Index Matching       : 0.00
% 6.46/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
