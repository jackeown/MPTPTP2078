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
% DateTime   : Thu Dec  3 10:05:58 EST 2020

% Result     : Theorem 26.70s
% Output     : CNFRefutation 26.70s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 556 expanded)
%              Number of leaves         :   37 ( 198 expanded)
%              Depth                    :   20
%              Number of atoms          :  187 ( 910 expanded)
%              Number of equality atoms :   69 ( 346 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_97,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_102,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_95,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_74,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_200,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | k4_xboole_0(A_77,B_78) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [A_47] : r2_hidden(A_47,k1_ordinal1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_131,plain,(
    ! [B_67,A_68] :
      ( ~ r1_tarski(B_67,A_68)
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_139,plain,(
    ! [A_47] : ~ r1_tarski(k1_ordinal1(A_47),A_47) ),
    inference(resolution,[status(thm)],[c_70,c_131])).

tff(c_214,plain,(
    ! [B_78] : k4_xboole_0(k1_ordinal1(B_78),B_78) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_200,c_139])).

tff(c_68,plain,(
    ! [A_46] : k2_xboole_0(A_46,k1_tarski(A_46)) = k1_ordinal1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1444,plain,(
    ! [A_161,B_162,C_163] :
      ( r1_tarski(k4_xboole_0(A_161,B_162),C_163)
      | ~ r1_tarski(A_161,k2_xboole_0(B_162,C_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6638,plain,(
    ! [A_375,B_376,C_377] :
      ( k4_xboole_0(k4_xboole_0(A_375,B_376),C_377) = k1_xboole_0
      | ~ r1_tarski(A_375,k2_xboole_0(B_376,C_377)) ) ),
    inference(resolution,[status(thm)],[c_1444,c_32])).

tff(c_6725,plain,(
    ! [B_378,C_379] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_378,C_379),B_378),C_379) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_6638])).

tff(c_6871,plain,(
    ! [A_380] : k4_xboole_0(k4_xboole_0(k1_ordinal1(A_380),A_380),k1_tarski(A_380)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6725])).

tff(c_66,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,k1_tarski(B_45)) = A_44
      | r2_hidden(B_45,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6917,plain,(
    ! [A_380] :
      ( k4_xboole_0(k1_ordinal1(A_380),A_380) = k1_xboole_0
      | r2_hidden(A_380,k4_xboole_0(k1_ordinal1(A_380),A_380)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6871,c_66])).

tff(c_6969,plain,(
    ! [A_380] : r2_hidden(A_380,k4_xboole_0(k1_ordinal1(A_380),A_380)) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_6917])).

tff(c_6844,plain,(
    ! [A_46] : k4_xboole_0(k4_xboole_0(k1_ordinal1(A_46),A_46),k1_tarski(A_46)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6725])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k1_tarski(A_40),B_41)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_846,plain,(
    ! [B_128,A_129] :
      ( B_128 = A_129
      | ~ r1_tarski(B_128,A_129)
      | ~ r1_tarski(A_129,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5151,plain,(
    ! [A_325,B_326] :
      ( k1_tarski(A_325) = B_326
      | ~ r1_tarski(B_326,k1_tarski(A_325))
      | ~ r2_hidden(A_325,B_326) ) ),
    inference(resolution,[status(thm)],[c_60,c_846])).

tff(c_36624,plain,(
    ! [A_876,A_877] :
      ( k1_tarski(A_876) = A_877
      | ~ r2_hidden(A_876,A_877)
      | k4_xboole_0(A_877,k1_tarski(A_876)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_5151])).

tff(c_36693,plain,(
    ! [A_46] :
      ( k4_xboole_0(k1_ordinal1(A_46),A_46) = k1_tarski(A_46)
      | ~ r2_hidden(A_46,k4_xboole_0(k1_ordinal1(A_46),A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6844,c_36624])).

tff(c_36771,plain,(
    ! [A_878] : k4_xboole_0(k1_ordinal1(A_878),A_878) = k1_tarski(A_878) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6969,c_36693])).

tff(c_42,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_115,plain,(
    ! [B_61,A_62] :
      ( r1_xboole_0(B_61,A_62)
      | ~ r1_xboole_0(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_118,plain,(
    ! [B_25,A_24] : r1_xboole_0(B_25,k4_xboole_0(A_24,B_25)) ),
    inference(resolution,[status(thm)],[c_42,c_115])).

tff(c_148,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = A_71
      | ~ r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_155,plain,(
    ! [B_25,A_24] : k4_xboole_0(B_25,k4_xboole_0(A_24,B_25)) = B_25 ),
    inference(resolution,[status(thm)],[c_118,c_148])).

tff(c_36989,plain,(
    ! [A_878] : k4_xboole_0(A_878,k1_tarski(A_878)) = A_878 ),
    inference(superposition,[status(thm),theory(equality)],[c_36771,c_155])).

tff(c_982,plain,(
    ! [A_142,B_143] : k4_xboole_0(k2_xboole_0(A_142,B_143),B_143) = k4_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1036,plain,(
    ! [A_46] : k4_xboole_0(k1_ordinal1(A_46),k1_tarski(A_46)) = k4_xboole_0(A_46,k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_982])).

tff(c_37193,plain,(
    ! [A_46] : k4_xboole_0(k1_ordinal1(A_46),k1_tarski(A_46)) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36989,c_1036])).

tff(c_184,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,B_76)
      | ~ r1_tarski(k1_tarski(A_75),B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_199,plain,(
    ! [A_75] : r2_hidden(A_75,k1_tarski(A_75)) ),
    inference(resolution,[status(thm)],[c_28,c_184])).

tff(c_298,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k1_xboole_0
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_326,plain,(
    ! [B_12] : k4_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_298])).

tff(c_698,plain,(
    ! [B_118,A_119] :
      ( ~ r2_hidden(B_118,A_119)
      | k4_xboole_0(A_119,k1_tarski(B_118)) != A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_710,plain,(
    ! [B_118] :
      ( ~ r2_hidden(B_118,k1_tarski(B_118))
      | k1_tarski(B_118) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_698])).

tff(c_713,plain,(
    ! [B_118] : k1_tarski(B_118) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_710])).

tff(c_76,plain,(
    k1_ordinal1('#skF_3') = k1_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2299,plain,(
    ! [D_188,A_189,B_190] :
      ( r2_hidden(D_188,k4_xboole_0(A_189,B_190))
      | r2_hidden(D_188,B_190)
      | ~ r2_hidden(D_188,A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_7165,plain,(
    ! [A_386,B_387,D_388] :
      ( ~ r2_hidden(k4_xboole_0(A_386,B_387),D_388)
      | r2_hidden(D_388,B_387)
      | ~ r2_hidden(D_388,A_386) ) ),
    inference(resolution,[status(thm)],[c_2299,c_2])).

tff(c_7202,plain,(
    ! [A_46,D_388] :
      ( ~ r2_hidden(k4_xboole_0(A_46,k1_tarski(A_46)),D_388)
      | r2_hidden(D_388,k1_tarski(A_46))
      | ~ r2_hidden(D_388,k1_ordinal1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_7165])).

tff(c_67239,plain,(
    ! [A_1302,D_1303] :
      ( ~ r2_hidden(A_1302,D_1303)
      | r2_hidden(D_1303,k1_tarski(A_1302))
      | ~ r2_hidden(D_1303,k1_ordinal1(A_1302)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36989,c_7202])).

tff(c_286,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(k1_tarski(A_95),B_96)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_215,plain,(
    ! [A_79] : r2_hidden(A_79,k1_tarski(A_79)) ),
    inference(resolution,[status(thm)],[c_28,c_184])).

tff(c_72,plain,(
    ! [B_49,A_48] :
      ( ~ r1_tarski(B_49,A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_221,plain,(
    ! [A_79] : ~ r1_tarski(k1_tarski(A_79),A_79) ),
    inference(resolution,[status(thm)],[c_215,c_72])).

tff(c_294,plain,(
    ! [B_96] : ~ r2_hidden(B_96,B_96) ),
    inference(resolution,[status(thm)],[c_286,c_221])).

tff(c_327,plain,(
    ! [B_101] : k4_xboole_0(B_101,B_101) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_298])).

tff(c_36,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_363,plain,(
    ! [B_105] : r1_tarski(k1_xboole_0,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_36])).

tff(c_367,plain,(
    ! [B_105] : k4_xboole_0(k1_xboole_0,B_105) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_363,c_32])).

tff(c_711,plain,(
    ! [B_118] : ~ r2_hidden(B_118,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_698])).

tff(c_320,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(k1_tarski(A_40),B_41) = k1_xboole_0
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_60,c_298])).

tff(c_1016,plain,(
    ! [A_142,B_143] : r1_tarski(k4_xboole_0(A_142,B_143),k2_xboole_0(A_142,B_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_36])).

tff(c_7781,plain,(
    ! [A_400,C_401,B_402] :
      ( r1_tarski(A_400,C_401)
      | ~ r1_tarski(A_400,k2_xboole_0(k1_tarski(B_402),C_401))
      | r2_hidden(B_402,A_400) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1444])).

tff(c_48315,plain,(
    ! [B_1030,B_1031] :
      ( r1_tarski(k4_xboole_0(k1_tarski(B_1030),B_1031),B_1031)
      | r2_hidden(B_1030,k4_xboole_0(k1_tarski(B_1030),B_1031)) ) ),
    inference(resolution,[status(thm)],[c_1016,c_7781])).

tff(c_48533,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k4_xboole_0(k1_tarski(A_40),B_41),B_41)
      | r2_hidden(A_40,k1_xboole_0)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_48315])).

tff(c_48631,plain,(
    ! [A_1032,B_1033] :
      ( r1_tarski(k4_xboole_0(k1_tarski(A_1032),B_1033),B_1033)
      | ~ r2_hidden(A_1032,B_1033) ) ),
    inference(negUnitSimplification,[status(thm)],[c_711,c_48533])).

tff(c_2392,plain,(
    ! [A_189,B_190,D_188] :
      ( ~ r1_tarski(k4_xboole_0(A_189,B_190),D_188)
      | r2_hidden(D_188,B_190)
      | ~ r2_hidden(D_188,A_189) ) ),
    inference(resolution,[status(thm)],[c_2299,c_72])).

tff(c_48655,plain,(
    ! [B_1033,A_1032] :
      ( r2_hidden(B_1033,B_1033)
      | ~ r2_hidden(B_1033,k1_tarski(A_1032))
      | ~ r2_hidden(A_1032,B_1033) ) ),
    inference(resolution,[status(thm)],[c_48631,c_2392])).

tff(c_48769,plain,(
    ! [B_1033,A_1032] :
      ( ~ r2_hidden(B_1033,k1_tarski(A_1032))
      | ~ r2_hidden(A_1032,B_1033) ) ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_48655])).

tff(c_67859,plain,(
    ! [A_1304,D_1305] :
      ( ~ r2_hidden(A_1304,D_1305)
      | ~ r2_hidden(D_1305,k1_ordinal1(A_1304)) ) ),
    inference(resolution,[status(thm)],[c_67239,c_48769])).

tff(c_68107,plain,(
    ! [D_1307] :
      ( ~ r2_hidden('#skF_3',D_1307)
      | ~ r2_hidden(D_1307,k1_ordinal1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_67859])).

tff(c_68246,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_68107])).

tff(c_755,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,k1_tarski(B_124)) = A_123
      | r2_hidden(B_124,A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_791,plain,(
    ! [B_124,A_123] :
      ( k4_xboole_0(k1_tarski(B_124),A_123) = k1_tarski(B_124)
      | r2_hidden(B_124,A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_155])).

tff(c_7017,plain,(
    ! [A_382] : r2_hidden(A_382,k4_xboole_0(k1_ordinal1(A_382),A_382)) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_6917])).

tff(c_7064,plain,(
    r2_hidden('#skF_3',k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_7017])).

tff(c_6958,plain,(
    k4_xboole_0(k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3'),k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_6871])).

tff(c_34,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | k4_xboole_0(B_16,A_15) != k4_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7657,plain,
    ( k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3') = k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_3'),k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6958,c_34])).

tff(c_15021,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7657])).

tff(c_15380,plain,(
    ~ r2_hidden('#skF_3',k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_15021])).

tff(c_15387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7064,c_15380])).

tff(c_15388,plain,(
    k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7657])).

tff(c_25100,plain,(
    ! [B_707,C_708,B_709] : k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(B_707,C_708),B_709),B_707),C_708) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_6638])).

tff(c_85425,plain,(
    ! [A_1554,B_1555] : k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_ordinal1(A_1554),B_1555),A_1554),k1_tarski(A_1554)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_25100])).

tff(c_85843,plain,(
    k4_xboole_0(k4_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15388,c_85425])).

tff(c_86974,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0
    | r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_85843])).

tff(c_87091,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68246,c_86974])).

tff(c_87340,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87091,c_791])).

tff(c_87537,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_87340])).

tff(c_87407,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87091,c_66])).

tff(c_87553,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_87407])).

tff(c_5208,plain,(
    ! [A_40,A_325] :
      ( k1_tarski(A_40) = k1_tarski(A_325)
      | ~ r2_hidden(A_325,k1_tarski(A_40))
      | ~ r2_hidden(A_40,k1_tarski(A_325)) ) ),
    inference(resolution,[status(thm)],[c_60,c_5151])).

tff(c_87740,plain,
    ( k1_tarski('#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_87553,c_5208])).

tff(c_87774,plain,(
    k1_tarski('#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87537,c_87740])).

tff(c_15484,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_15388,c_155])).

tff(c_3642,plain,(
    ! [A_275] : k4_xboole_0(k1_ordinal1(A_275),k1_tarski(A_275)) = k4_xboole_0(A_275,k1_tarski(A_275)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_982])).

tff(c_3702,plain,(
    k4_xboole_0(k1_ordinal1('#skF_4'),k1_tarski('#skF_3')) = k4_xboole_0('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_3642])).

tff(c_15644,plain,(
    k4_xboole_0(k1_ordinal1('#skF_4'),k1_tarski('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15484,c_3702])).

tff(c_88449,plain,(
    k4_xboole_0(k1_ordinal1('#skF_4'),k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87774,c_15644])).

tff(c_88460,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37193,c_88449])).

tff(c_88462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_88460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:23:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.70/17.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.70/17.24  
% 26.70/17.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.70/17.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 26.70/17.24  
% 26.70/17.24  %Foreground sorts:
% 26.70/17.24  
% 26.70/17.24  
% 26.70/17.24  %Background operators:
% 26.70/17.24  
% 26.70/17.24  
% 26.70/17.24  %Foreground operators:
% 26.70/17.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 26.70/17.24  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 26.70/17.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.70/17.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.70/17.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 26.70/17.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.70/17.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.70/17.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 26.70/17.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.70/17.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 26.70/17.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 26.70/17.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 26.70/17.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.70/17.24  tff('#skF_3', type, '#skF_3': $i).
% 26.70/17.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.70/17.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.70/17.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 26.70/17.24  tff('#skF_4', type, '#skF_4': $i).
% 26.70/17.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.70/17.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.70/17.24  
% 26.70/17.26  tff(f_107, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_ordinal1)).
% 26.70/17.26  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 26.70/17.26  tff(f_97, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 26.70/17.26  tff(f_102, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 26.70/17.26  tff(f_95, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 26.70/17.26  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 26.70/17.26  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 26.70/17.26  tff(f_93, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 26.70/17.26  tff(f_86, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 26.70/17.26  tff(f_68, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 26.70/17.26  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 26.70/17.26  tff(f_74, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 26.70/17.26  tff(f_62, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 26.70/17.26  tff(f_40, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 26.70/17.26  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 26.70/17.26  tff(f_60, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 26.70/17.26  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 26.70/17.26  tff(c_74, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 26.70/17.26  tff(c_200, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | k4_xboole_0(A_77, B_78)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 26.70/17.26  tff(c_70, plain, (![A_47]: (r2_hidden(A_47, k1_ordinal1(A_47)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 26.70/17.26  tff(c_131, plain, (![B_67, A_68]: (~r1_tarski(B_67, A_68) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_102])).
% 26.70/17.26  tff(c_139, plain, (![A_47]: (~r1_tarski(k1_ordinal1(A_47), A_47))), inference(resolution, [status(thm)], [c_70, c_131])).
% 26.70/17.26  tff(c_214, plain, (![B_78]: (k4_xboole_0(k1_ordinal1(B_78), B_78)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_200, c_139])).
% 26.70/17.26  tff(c_68, plain, (![A_46]: (k2_xboole_0(A_46, k1_tarski(A_46))=k1_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.70/17.26  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 26.70/17.26  tff(c_1444, plain, (![A_161, B_162, C_163]: (r1_tarski(k4_xboole_0(A_161, B_162), C_163) | ~r1_tarski(A_161, k2_xboole_0(B_162, C_163)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 26.70/17.26  tff(c_32, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 26.70/17.26  tff(c_6638, plain, (![A_375, B_376, C_377]: (k4_xboole_0(k4_xboole_0(A_375, B_376), C_377)=k1_xboole_0 | ~r1_tarski(A_375, k2_xboole_0(B_376, C_377)))), inference(resolution, [status(thm)], [c_1444, c_32])).
% 26.70/17.26  tff(c_6725, plain, (![B_378, C_379]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_378, C_379), B_378), C_379)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_6638])).
% 26.70/17.26  tff(c_6871, plain, (![A_380]: (k4_xboole_0(k4_xboole_0(k1_ordinal1(A_380), A_380), k1_tarski(A_380))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_6725])).
% 26.70/17.26  tff(c_66, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k1_tarski(B_45))=A_44 | r2_hidden(B_45, A_44))), inference(cnfTransformation, [status(thm)], [f_93])).
% 26.70/17.26  tff(c_6917, plain, (![A_380]: (k4_xboole_0(k1_ordinal1(A_380), A_380)=k1_xboole_0 | r2_hidden(A_380, k4_xboole_0(k1_ordinal1(A_380), A_380)))), inference(superposition, [status(thm), theory('equality')], [c_6871, c_66])).
% 26.70/17.26  tff(c_6969, plain, (![A_380]: (r2_hidden(A_380, k4_xboole_0(k1_ordinal1(A_380), A_380)))), inference(negUnitSimplification, [status(thm)], [c_214, c_6917])).
% 26.70/17.26  tff(c_6844, plain, (![A_46]: (k4_xboole_0(k4_xboole_0(k1_ordinal1(A_46), A_46), k1_tarski(A_46))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_6725])).
% 26.70/17.26  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 26.70/17.26  tff(c_60, plain, (![A_40, B_41]: (r1_tarski(k1_tarski(A_40), B_41) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_86])).
% 26.70/17.26  tff(c_846, plain, (![B_128, A_129]: (B_128=A_129 | ~r1_tarski(B_128, A_129) | ~r1_tarski(A_129, B_128))), inference(cnfTransformation, [status(thm)], [f_50])).
% 26.70/17.26  tff(c_5151, plain, (![A_325, B_326]: (k1_tarski(A_325)=B_326 | ~r1_tarski(B_326, k1_tarski(A_325)) | ~r2_hidden(A_325, B_326))), inference(resolution, [status(thm)], [c_60, c_846])).
% 26.70/17.26  tff(c_36624, plain, (![A_876, A_877]: (k1_tarski(A_876)=A_877 | ~r2_hidden(A_876, A_877) | k4_xboole_0(A_877, k1_tarski(A_876))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_5151])).
% 26.70/17.26  tff(c_36693, plain, (![A_46]: (k4_xboole_0(k1_ordinal1(A_46), A_46)=k1_tarski(A_46) | ~r2_hidden(A_46, k4_xboole_0(k1_ordinal1(A_46), A_46)))), inference(superposition, [status(thm), theory('equality')], [c_6844, c_36624])).
% 26.70/17.26  tff(c_36771, plain, (![A_878]: (k4_xboole_0(k1_ordinal1(A_878), A_878)=k1_tarski(A_878))), inference(demodulation, [status(thm), theory('equality')], [c_6969, c_36693])).
% 26.70/17.26  tff(c_42, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 26.70/17.26  tff(c_115, plain, (![B_61, A_62]: (r1_xboole_0(B_61, A_62) | ~r1_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 26.70/17.26  tff(c_118, plain, (![B_25, A_24]: (r1_xboole_0(B_25, k4_xboole_0(A_24, B_25)))), inference(resolution, [status(thm)], [c_42, c_115])).
% 26.70/17.26  tff(c_148, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=A_71 | ~r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_74])).
% 26.70/17.26  tff(c_155, plain, (![B_25, A_24]: (k4_xboole_0(B_25, k4_xboole_0(A_24, B_25))=B_25)), inference(resolution, [status(thm)], [c_118, c_148])).
% 26.70/17.26  tff(c_36989, plain, (![A_878]: (k4_xboole_0(A_878, k1_tarski(A_878))=A_878)), inference(superposition, [status(thm), theory('equality')], [c_36771, c_155])).
% 26.70/17.26  tff(c_982, plain, (![A_142, B_143]: (k4_xboole_0(k2_xboole_0(A_142, B_143), B_143)=k4_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_62])).
% 26.70/17.26  tff(c_1036, plain, (![A_46]: (k4_xboole_0(k1_ordinal1(A_46), k1_tarski(A_46))=k4_xboole_0(A_46, k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_982])).
% 26.70/17.26  tff(c_37193, plain, (![A_46]: (k4_xboole_0(k1_ordinal1(A_46), k1_tarski(A_46))=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_36989, c_1036])).
% 26.70/17.26  tff(c_184, plain, (![A_75, B_76]: (r2_hidden(A_75, B_76) | ~r1_tarski(k1_tarski(A_75), B_76))), inference(cnfTransformation, [status(thm)], [f_86])).
% 26.70/17.26  tff(c_199, plain, (![A_75]: (r2_hidden(A_75, k1_tarski(A_75)))), inference(resolution, [status(thm)], [c_28, c_184])).
% 26.70/17.26  tff(c_298, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k1_xboole_0 | ~r1_tarski(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_54])).
% 26.70/17.26  tff(c_326, plain, (![B_12]: (k4_xboole_0(B_12, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_298])).
% 26.70/17.26  tff(c_698, plain, (![B_118, A_119]: (~r2_hidden(B_118, A_119) | k4_xboole_0(A_119, k1_tarski(B_118))!=A_119)), inference(cnfTransformation, [status(thm)], [f_93])).
% 26.70/17.26  tff(c_710, plain, (![B_118]: (~r2_hidden(B_118, k1_tarski(B_118)) | k1_tarski(B_118)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_326, c_698])).
% 26.70/17.26  tff(c_713, plain, (![B_118]: (k1_tarski(B_118)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_710])).
% 26.70/17.26  tff(c_76, plain, (k1_ordinal1('#skF_3')=k1_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 26.70/17.26  tff(c_2299, plain, (![D_188, A_189, B_190]: (r2_hidden(D_188, k4_xboole_0(A_189, B_190)) | r2_hidden(D_188, B_190) | ~r2_hidden(D_188, A_189))), inference(cnfTransformation, [status(thm)], [f_40])).
% 26.70/17.26  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 26.70/17.26  tff(c_7165, plain, (![A_386, B_387, D_388]: (~r2_hidden(k4_xboole_0(A_386, B_387), D_388) | r2_hidden(D_388, B_387) | ~r2_hidden(D_388, A_386))), inference(resolution, [status(thm)], [c_2299, c_2])).
% 26.70/17.26  tff(c_7202, plain, (![A_46, D_388]: (~r2_hidden(k4_xboole_0(A_46, k1_tarski(A_46)), D_388) | r2_hidden(D_388, k1_tarski(A_46)) | ~r2_hidden(D_388, k1_ordinal1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_1036, c_7165])).
% 26.70/17.26  tff(c_67239, plain, (![A_1302, D_1303]: (~r2_hidden(A_1302, D_1303) | r2_hidden(D_1303, k1_tarski(A_1302)) | ~r2_hidden(D_1303, k1_ordinal1(A_1302)))), inference(demodulation, [status(thm), theory('equality')], [c_36989, c_7202])).
% 26.70/17.26  tff(c_286, plain, (![A_95, B_96]: (r1_tarski(k1_tarski(A_95), B_96) | ~r2_hidden(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_86])).
% 26.70/17.26  tff(c_215, plain, (![A_79]: (r2_hidden(A_79, k1_tarski(A_79)))), inference(resolution, [status(thm)], [c_28, c_184])).
% 26.70/17.26  tff(c_72, plain, (![B_49, A_48]: (~r1_tarski(B_49, A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_102])).
% 26.70/17.26  tff(c_221, plain, (![A_79]: (~r1_tarski(k1_tarski(A_79), A_79))), inference(resolution, [status(thm)], [c_215, c_72])).
% 26.70/17.26  tff(c_294, plain, (![B_96]: (~r2_hidden(B_96, B_96))), inference(resolution, [status(thm)], [c_286, c_221])).
% 26.70/17.26  tff(c_327, plain, (![B_101]: (k4_xboole_0(B_101, B_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_298])).
% 26.70/17.26  tff(c_36, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 26.70/17.26  tff(c_363, plain, (![B_105]: (r1_tarski(k1_xboole_0, B_105))), inference(superposition, [status(thm), theory('equality')], [c_327, c_36])).
% 26.70/17.26  tff(c_367, plain, (![B_105]: (k4_xboole_0(k1_xboole_0, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_363, c_32])).
% 26.70/17.26  tff(c_711, plain, (![B_118]: (~r2_hidden(B_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_367, c_698])).
% 26.70/17.26  tff(c_320, plain, (![A_40, B_41]: (k4_xboole_0(k1_tarski(A_40), B_41)=k1_xboole_0 | ~r2_hidden(A_40, B_41))), inference(resolution, [status(thm)], [c_60, c_298])).
% 26.70/17.26  tff(c_1016, plain, (![A_142, B_143]: (r1_tarski(k4_xboole_0(A_142, B_143), k2_xboole_0(A_142, B_143)))), inference(superposition, [status(thm), theory('equality')], [c_982, c_36])).
% 26.70/17.26  tff(c_7781, plain, (![A_400, C_401, B_402]: (r1_tarski(A_400, C_401) | ~r1_tarski(A_400, k2_xboole_0(k1_tarski(B_402), C_401)) | r2_hidden(B_402, A_400))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1444])).
% 26.70/17.26  tff(c_48315, plain, (![B_1030, B_1031]: (r1_tarski(k4_xboole_0(k1_tarski(B_1030), B_1031), B_1031) | r2_hidden(B_1030, k4_xboole_0(k1_tarski(B_1030), B_1031)))), inference(resolution, [status(thm)], [c_1016, c_7781])).
% 26.70/17.26  tff(c_48533, plain, (![A_40, B_41]: (r1_tarski(k4_xboole_0(k1_tarski(A_40), B_41), B_41) | r2_hidden(A_40, k1_xboole_0) | ~r2_hidden(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_320, c_48315])).
% 26.70/17.26  tff(c_48631, plain, (![A_1032, B_1033]: (r1_tarski(k4_xboole_0(k1_tarski(A_1032), B_1033), B_1033) | ~r2_hidden(A_1032, B_1033))), inference(negUnitSimplification, [status(thm)], [c_711, c_48533])).
% 26.70/17.26  tff(c_2392, plain, (![A_189, B_190, D_188]: (~r1_tarski(k4_xboole_0(A_189, B_190), D_188) | r2_hidden(D_188, B_190) | ~r2_hidden(D_188, A_189))), inference(resolution, [status(thm)], [c_2299, c_72])).
% 26.70/17.26  tff(c_48655, plain, (![B_1033, A_1032]: (r2_hidden(B_1033, B_1033) | ~r2_hidden(B_1033, k1_tarski(A_1032)) | ~r2_hidden(A_1032, B_1033))), inference(resolution, [status(thm)], [c_48631, c_2392])).
% 26.70/17.26  tff(c_48769, plain, (![B_1033, A_1032]: (~r2_hidden(B_1033, k1_tarski(A_1032)) | ~r2_hidden(A_1032, B_1033))), inference(negUnitSimplification, [status(thm)], [c_294, c_48655])).
% 26.70/17.26  tff(c_67859, plain, (![A_1304, D_1305]: (~r2_hidden(A_1304, D_1305) | ~r2_hidden(D_1305, k1_ordinal1(A_1304)))), inference(resolution, [status(thm)], [c_67239, c_48769])).
% 26.70/17.26  tff(c_68107, plain, (![D_1307]: (~r2_hidden('#skF_3', D_1307) | ~r2_hidden(D_1307, k1_ordinal1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_67859])).
% 26.70/17.26  tff(c_68246, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_68107])).
% 26.70/17.26  tff(c_755, plain, (![A_123, B_124]: (k4_xboole_0(A_123, k1_tarski(B_124))=A_123 | r2_hidden(B_124, A_123))), inference(cnfTransformation, [status(thm)], [f_93])).
% 26.70/17.26  tff(c_791, plain, (![B_124, A_123]: (k4_xboole_0(k1_tarski(B_124), A_123)=k1_tarski(B_124) | r2_hidden(B_124, A_123))), inference(superposition, [status(thm), theory('equality')], [c_755, c_155])).
% 26.70/17.26  tff(c_7017, plain, (![A_382]: (r2_hidden(A_382, k4_xboole_0(k1_ordinal1(A_382), A_382)))), inference(negUnitSimplification, [status(thm)], [c_214, c_6917])).
% 26.70/17.26  tff(c_7064, plain, (r2_hidden('#skF_3', k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_7017])).
% 26.70/17.26  tff(c_6958, plain, (k4_xboole_0(k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'), k1_tarski('#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_76, c_6871])).
% 26.70/17.26  tff(c_34, plain, (![B_16, A_15]: (B_16=A_15 | k4_xboole_0(B_16, A_15)!=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 26.70/17.26  tff(c_7657, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3')=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_3'), k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6958, c_34])).
% 26.70/17.26  tff(c_15021, plain, (k4_xboole_0(k1_tarski('#skF_3'), k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7657])).
% 26.70/17.26  tff(c_15380, plain, (~r2_hidden('#skF_3', k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_320, c_15021])).
% 26.70/17.26  tff(c_15387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7064, c_15380])).
% 26.70/17.26  tff(c_15388, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_7657])).
% 26.70/17.26  tff(c_25100, plain, (![B_707, C_708, B_709]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(B_707, C_708), B_709), B_707), C_708)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_6638])).
% 26.70/17.26  tff(c_85425, plain, (![A_1554, B_1555]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_ordinal1(A_1554), B_1555), A_1554), k1_tarski(A_1554))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_25100])).
% 26.70/17.26  tff(c_85843, plain, (k4_xboole_0(k4_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_tarski('#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15388, c_85425])).
% 26.70/17.26  tff(c_86974, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0 | r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_791, c_85843])).
% 26.70/17.26  tff(c_87091, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68246, c_86974])).
% 26.70/17.26  tff(c_87340, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_87091, c_791])).
% 26.70/17.26  tff(c_87537, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_713, c_87340])).
% 26.70/17.26  tff(c_87407, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_87091, c_66])).
% 26.70/17.26  tff(c_87553, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_713, c_87407])).
% 26.70/17.26  tff(c_5208, plain, (![A_40, A_325]: (k1_tarski(A_40)=k1_tarski(A_325) | ~r2_hidden(A_325, k1_tarski(A_40)) | ~r2_hidden(A_40, k1_tarski(A_325)))), inference(resolution, [status(thm)], [c_60, c_5151])).
% 26.70/17.26  tff(c_87740, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_87553, c_5208])).
% 26.70/17.26  tff(c_87774, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87537, c_87740])).
% 26.70/17.26  tff(c_15484, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_15388, c_155])).
% 26.70/17.26  tff(c_3642, plain, (![A_275]: (k4_xboole_0(k1_ordinal1(A_275), k1_tarski(A_275))=k4_xboole_0(A_275, k1_tarski(A_275)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_982])).
% 26.70/17.26  tff(c_3702, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), k1_tarski('#skF_3'))=k4_xboole_0('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_3642])).
% 26.70/17.26  tff(c_15644, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), k1_tarski('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15484, c_3702])).
% 26.70/17.26  tff(c_88449, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_87774, c_15644])).
% 26.70/17.26  tff(c_88460, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37193, c_88449])).
% 26.70/17.26  tff(c_88462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_88460])).
% 26.70/17.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.70/17.26  
% 26.70/17.26  Inference rules
% 26.70/17.26  ----------------------
% 26.70/17.26  #Ref     : 7
% 26.70/17.26  #Sup     : 21427
% 26.70/17.26  #Fact    : 0
% 26.70/17.26  #Define  : 0
% 26.70/17.26  #Split   : 11
% 26.70/17.26  #Chain   : 0
% 26.70/17.26  #Close   : 0
% 26.70/17.26  
% 26.70/17.26  Ordering : KBO
% 26.70/17.26  
% 26.70/17.26  Simplification rules
% 26.70/17.26  ----------------------
% 26.70/17.26  #Subsume      : 10749
% 26.70/17.26  #Demod        : 10340
% 26.70/17.26  #Tautology    : 4112
% 26.70/17.26  #SimpNegUnit  : 1425
% 26.70/17.26  #BackRed      : 265
% 26.70/17.26  
% 26.70/17.26  #Partial instantiations: 0
% 26.70/17.26  #Strategies tried      : 1
% 26.70/17.26  
% 26.70/17.26  Timing (in seconds)
% 26.70/17.26  ----------------------
% 26.70/17.26  Preprocessing        : 0.34
% 26.92/17.26  Parsing              : 0.18
% 26.92/17.26  CNF conversion       : 0.02
% 26.92/17.26  Main loop            : 16.14
% 26.92/17.26  Inferencing          : 1.93
% 26.92/17.26  Reduction            : 7.67
% 26.92/17.26  Demodulation         : 5.12
% 26.92/17.26  BG Simplification    : 0.18
% 26.92/17.26  Subsumption          : 5.59
% 26.92/17.26  Abstraction          : 0.29
% 26.92/17.26  MUC search           : 0.00
% 26.92/17.26  Cooper               : 0.00
% 26.92/17.26  Total                : 16.53
% 26.92/17.27  Index Insertion      : 0.00
% 26.92/17.27  Index Deletion       : 0.00
% 26.92/17.27  Index Matching       : 0.00
% 26.92/17.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
