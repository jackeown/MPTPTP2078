%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:10 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 687 expanded)
%              Number of leaves         :   43 ( 249 expanded)
%              Depth                    :   23
%              Number of atoms          :  148 ( 944 expanded)
%              Number of equality atoms :  108 ( 625 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_50,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_20,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    ! [A_67] :
      ( k1_xboole_0 = A_67
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_84])).

tff(c_62,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_170,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62])).

tff(c_171,plain,(
    '#skF_5' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_163,plain,
    ( '#skF_6' != '#skF_3'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60])).

tff(c_164,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_66,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_165,plain,(
    ! [A_76,B_77] : r1_tarski(A_76,k2_xboole_0(A_76,B_77)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_168,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_165])).

tff(c_52,plain,(
    ! [B_61,A_60] :
      ( k1_tarski(B_61) = A_60
      | k1_xboole_0 = A_60
      | ~ r1_tarski(A_60,k1_tarski(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_636,plain,(
    ! [B_114,A_115] :
      ( k1_tarski(B_114) = A_115
      | A_115 = '#skF_3'
      | ~ r1_tarski(A_115,k1_tarski(B_114)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_52])).

tff(c_647,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_168,c_636])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_164,c_647])).

tff(c_658,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_908,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_2'(A_129,B_130),A_129)
      | r1_tarski(A_129,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_912,plain,(
    ! [A_129,B_130] :
      ( ~ v1_xboole_0(A_129)
      | r1_tarski(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_908,c_6])).

tff(c_30,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_111,plain,(
    ! [A_24] : k5_xboole_0(A_24,'#skF_3') = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_30])).

tff(c_24,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,(
    ! [A_19] : k3_xboole_0(A_19,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_24])).

tff(c_933,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k3_xboole_0(A_135,B_136)) = k4_xboole_0(A_135,B_136) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_959,plain,(
    ! [A_19] : k5_xboole_0(A_19,'#skF_3') = k4_xboole_0(A_19,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_933])).

tff(c_968,plain,(
    ! [A_19] : k4_xboole_0(A_19,'#skF_3') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_959])).

tff(c_1140,plain,(
    ! [A_147,B_148] :
      ( k2_xboole_0(A_147,k4_xboole_0(B_148,A_147)) = B_148
      | ~ r1_tarski(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1216,plain,(
    ! [A_155] :
      ( k2_xboole_0('#skF_3',A_155) = A_155
      | ~ r1_tarski('#skF_3',A_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_1140])).

tff(c_1224,plain,(
    ! [B_130] :
      ( k2_xboole_0('#skF_3',B_130) = B_130
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_912,c_1216])).

tff(c_1240,plain,(
    ! [B_130] : k2_xboole_0('#skF_3',B_130) = B_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1224])).

tff(c_659,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_662,plain,(
    k2_xboole_0('#skF_3','#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_66])).

tff(c_1246,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_662])).

tff(c_1248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_1246])).

tff(c_1249,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_1250,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_64,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1278,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_1250,c_64])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1284,plain,(
    ! [B_160,A_161] : k5_xboole_0(B_160,A_161) = k5_xboole_0(A_161,B_160) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1300,plain,(
    ! [A_161] : k5_xboole_0('#skF_3',A_161) = A_161 ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_111])).

tff(c_1368,plain,(
    ! [B_163,A_164] : k3_xboole_0(B_163,A_164) = k3_xboole_0(A_164,B_163) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1406,plain,(
    ! [A_19] : k3_xboole_0('#skF_3',A_19) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1368])).

tff(c_1553,plain,(
    ! [A_178,B_179] : k5_xboole_0(A_178,k3_xboole_0(A_178,B_179)) = k4_xboole_0(A_178,B_179) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1560,plain,(
    ! [B_179] : k4_xboole_0('#skF_3',B_179) = k3_xboole_0('#skF_3',B_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_1553,c_1300])).

tff(c_1584,plain,(
    ! [B_179] : k4_xboole_0('#skF_3',B_179) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_1560])).

tff(c_1547,plain,(
    ! [A_174,B_175] :
      ( r2_hidden('#skF_2'(A_174,B_175),A_174)
      | r1_tarski(A_174,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1551,plain,(
    ! [A_174,B_175] :
      ( ~ v1_xboole_0(A_174)
      | r1_tarski(A_174,B_175) ) ),
    inference(resolution,[status(thm)],[c_1547,c_6])).

tff(c_1579,plain,(
    ! [A_19] : k5_xboole_0(A_19,'#skF_3') = k4_xboole_0(A_19,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1553])).

tff(c_1588,plain,(
    ! [A_19] : k4_xboole_0(A_19,'#skF_3') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1579])).

tff(c_1819,plain,(
    ! [A_199,B_200] :
      ( k2_xboole_0(A_199,k4_xboole_0(B_200,A_199)) = B_200
      | ~ r1_tarski(A_199,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1866,plain,(
    ! [A_202] :
      ( k2_xboole_0('#skF_3',A_202) = A_202
      | ~ r1_tarski('#skF_3',A_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1588,c_1819])).

tff(c_1874,plain,(
    ! [B_175] :
      ( k2_xboole_0('#skF_3',B_175) = B_175
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1551,c_1866])).

tff(c_1900,plain,(
    ! [B_203] : k2_xboole_0('#skF_3',B_203) = B_203 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1874])).

tff(c_26,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1914,plain,(
    ! [B_203] : k4_xboole_0(B_203,B_203) = k4_xboole_0('#skF_3',B_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_26])).

tff(c_1932,plain,(
    ! [B_203] : k4_xboole_0(B_203,B_203) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1914])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1582,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k4_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1553])).

tff(c_2032,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1932,c_1582])).

tff(c_2168,plain,(
    ! [A_211,B_212,C_213] : k5_xboole_0(k5_xboole_0(A_211,B_212),C_213) = k5_xboole_0(A_211,k5_xboole_0(B_212,C_213)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2212,plain,(
    ! [A_14,C_213] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_213)) = k5_xboole_0('#skF_3',C_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_2032,c_2168])).

tff(c_2273,plain,(
    ! [A_214,C_215] : k5_xboole_0(A_214,k5_xboole_0(A_214,C_215)) = C_215 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_2212])).

tff(c_2328,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2273])).

tff(c_2347,plain,(
    ! [A_216,B_217] : k5_xboole_0(A_216,k5_xboole_0(B_217,A_216)) = B_217 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2273])).

tff(c_2377,plain,(
    ! [B_4,A_3] : k5_xboole_0(k5_xboole_0(B_4,A_3),B_4) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_2328,c_2347])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1251,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_66])).

tff(c_1572,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1553])).

tff(c_36,plain,(
    ! [A_30,B_31] : k5_xboole_0(k5_xboole_0(A_30,B_31),k3_xboole_0(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2222,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k5_xboole_0(B_31,k3_xboole_0(A_30,B_31))) = k2_xboole_0(A_30,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2168])).

tff(c_2680,plain,(
    ! [A_226,B_227] : k5_xboole_0(A_226,k4_xboole_0(B_227,A_226)) = k2_xboole_0(A_226,B_227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_2222])).

tff(c_2267,plain,(
    ! [A_14,C_213] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_213)) = C_213 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_2212])).

tff(c_2975,plain,(
    ! [A_252,B_253] : k5_xboole_0(A_252,k2_xboole_0(A_252,B_253)) = k4_xboole_0(B_253,A_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_2680,c_2267])).

tff(c_3033,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1251,c_2975])).

tff(c_3043,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2032,c_3033])).

tff(c_2315,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k4_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_1572,c_2273])).

tff(c_3047,plain,(
    k5_xboole_0('#skF_6','#skF_3') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3043,c_2315])).

tff(c_3059,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_111,c_3047])).

tff(c_3080,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_5'),'#skF_6') = k2_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3059,c_36])).

tff(c_3089,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2377,c_3080])).

tff(c_32,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3140,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3089,c_32])).

tff(c_1777,plain,(
    ! [B_196,A_197] :
      ( k1_tarski(B_196) = A_197
      | A_197 = '#skF_3'
      | ~ r1_tarski(A_197,k1_tarski(B_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_52])).

tff(c_1788,plain,(
    ! [A_197] :
      ( k1_tarski('#skF_4') = A_197
      | A_197 = '#skF_3'
      | ~ r1_tarski(A_197,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_1777])).

tff(c_1795,plain,(
    ! [A_197] :
      ( A_197 = '#skF_5'
      | A_197 = '#skF_3'
      | ~ r1_tarski(A_197,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_1788])).

tff(c_3148,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3140,c_1795])).

tff(c_3152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1249,c_1278,c_3148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.70  
% 3.91/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.70  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.91/1.70  
% 3.91/1.70  %Foreground sorts:
% 3.91/1.70  
% 3.91/1.70  
% 3.91/1.70  %Background operators:
% 3.91/1.70  
% 3.91/1.70  
% 3.91/1.70  %Foreground operators:
% 3.91/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.91/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.91/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.91/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.91/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.91/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.91/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.91/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.91/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.91/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.91/1.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.91/1.70  
% 3.91/1.72  tff(f_50, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.91/1.72  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.91/1.72  tff(f_109, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.91/1.72  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.91/1.72  tff(f_88, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.91/1.72  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.91/1.72  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.91/1.72  tff(f_62, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.91/1.72  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.91/1.72  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.91/1.72  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.91/1.72  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.91/1.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.91/1.72  tff(f_56, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.91/1.72  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.91/1.72  tff(f_66, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.91/1.72  tff(f_68, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.91/1.72  tff(c_20, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.91/1.72  tff(c_84, plain, (![A_67]: (k1_xboole_0=A_67 | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.91/1.72  tff(c_88, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_20, c_84])).
% 3.91/1.72  tff(c_62, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.91/1.72  tff(c_170, plain, (k1_tarski('#skF_4')!='#skF_6' | '#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62])).
% 3.91/1.72  tff(c_171, plain, ('#skF_5'!='#skF_3'), inference(splitLeft, [status(thm)], [c_170])).
% 3.91/1.72  tff(c_60, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.91/1.72  tff(c_163, plain, ('#skF_6'!='#skF_3' | k1_tarski('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60])).
% 3.91/1.72  tff(c_164, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_163])).
% 3.91/1.72  tff(c_66, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.91/1.72  tff(c_165, plain, (![A_76, B_77]: (r1_tarski(A_76, k2_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.91/1.72  tff(c_168, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_165])).
% 3.91/1.72  tff(c_52, plain, (![B_61, A_60]: (k1_tarski(B_61)=A_60 | k1_xboole_0=A_60 | ~r1_tarski(A_60, k1_tarski(B_61)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.91/1.72  tff(c_636, plain, (![B_114, A_115]: (k1_tarski(B_114)=A_115 | A_115='#skF_3' | ~r1_tarski(A_115, k1_tarski(B_114)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_52])).
% 3.91/1.72  tff(c_647, plain, (k1_tarski('#skF_4')='#skF_5' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_168, c_636])).
% 3.91/1.72  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_164, c_647])).
% 3.91/1.72  tff(c_658, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_170])).
% 3.91/1.72  tff(c_908, plain, (![A_129, B_130]: (r2_hidden('#skF_2'(A_129, B_130), A_129) | r1_tarski(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.91/1.72  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.72  tff(c_912, plain, (![A_129, B_130]: (~v1_xboole_0(A_129) | r1_tarski(A_129, B_130))), inference(resolution, [status(thm)], [c_908, c_6])).
% 3.91/1.72  tff(c_30, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.91/1.72  tff(c_111, plain, (![A_24]: (k5_xboole_0(A_24, '#skF_3')=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_30])).
% 3.91/1.72  tff(c_24, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.72  tff(c_110, plain, (![A_19]: (k3_xboole_0(A_19, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_24])).
% 3.91/1.72  tff(c_933, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k3_xboole_0(A_135, B_136))=k4_xboole_0(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.91/1.72  tff(c_959, plain, (![A_19]: (k5_xboole_0(A_19, '#skF_3')=k4_xboole_0(A_19, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_933])).
% 3.91/1.72  tff(c_968, plain, (![A_19]: (k4_xboole_0(A_19, '#skF_3')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_959])).
% 3.91/1.72  tff(c_1140, plain, (![A_147, B_148]: (k2_xboole_0(A_147, k4_xboole_0(B_148, A_147))=B_148 | ~r1_tarski(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.91/1.72  tff(c_1216, plain, (![A_155]: (k2_xboole_0('#skF_3', A_155)=A_155 | ~r1_tarski('#skF_3', A_155))), inference(superposition, [status(thm), theory('equality')], [c_968, c_1140])).
% 3.91/1.72  tff(c_1224, plain, (![B_130]: (k2_xboole_0('#skF_3', B_130)=B_130 | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_912, c_1216])).
% 3.91/1.72  tff(c_1240, plain, (![B_130]: (k2_xboole_0('#skF_3', B_130)=B_130)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1224])).
% 3.91/1.72  tff(c_659, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_170])).
% 3.91/1.72  tff(c_662, plain, (k2_xboole_0('#skF_3', '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_66])).
% 3.91/1.72  tff(c_1246, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_662])).
% 3.91/1.72  tff(c_1248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_658, c_1246])).
% 3.91/1.72  tff(c_1249, plain, ('#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_163])).
% 3.91/1.72  tff(c_1250, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_163])).
% 3.91/1.72  tff(c_64, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.91/1.72  tff(c_1278, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_1250, c_64])).
% 3.91/1.72  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.91/1.72  tff(c_1284, plain, (![B_160, A_161]: (k5_xboole_0(B_160, A_161)=k5_xboole_0(A_161, B_160))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.91/1.72  tff(c_1300, plain, (![A_161]: (k5_xboole_0('#skF_3', A_161)=A_161)), inference(superposition, [status(thm), theory('equality')], [c_1284, c_111])).
% 3.91/1.72  tff(c_1368, plain, (![B_163, A_164]: (k3_xboole_0(B_163, A_164)=k3_xboole_0(A_164, B_163))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.91/1.72  tff(c_1406, plain, (![A_19]: (k3_xboole_0('#skF_3', A_19)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_110, c_1368])).
% 3.91/1.72  tff(c_1553, plain, (![A_178, B_179]: (k5_xboole_0(A_178, k3_xboole_0(A_178, B_179))=k4_xboole_0(A_178, B_179))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.91/1.72  tff(c_1560, plain, (![B_179]: (k4_xboole_0('#skF_3', B_179)=k3_xboole_0('#skF_3', B_179))), inference(superposition, [status(thm), theory('equality')], [c_1553, c_1300])).
% 3.91/1.72  tff(c_1584, plain, (![B_179]: (k4_xboole_0('#skF_3', B_179)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_1560])).
% 3.91/1.72  tff(c_1547, plain, (![A_174, B_175]: (r2_hidden('#skF_2'(A_174, B_175), A_174) | r1_tarski(A_174, B_175))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.91/1.72  tff(c_1551, plain, (![A_174, B_175]: (~v1_xboole_0(A_174) | r1_tarski(A_174, B_175))), inference(resolution, [status(thm)], [c_1547, c_6])).
% 3.91/1.72  tff(c_1579, plain, (![A_19]: (k5_xboole_0(A_19, '#skF_3')=k4_xboole_0(A_19, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_1553])).
% 3.91/1.72  tff(c_1588, plain, (![A_19]: (k4_xboole_0(A_19, '#skF_3')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1579])).
% 3.91/1.72  tff(c_1819, plain, (![A_199, B_200]: (k2_xboole_0(A_199, k4_xboole_0(B_200, A_199))=B_200 | ~r1_tarski(A_199, B_200))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.91/1.72  tff(c_1866, plain, (![A_202]: (k2_xboole_0('#skF_3', A_202)=A_202 | ~r1_tarski('#skF_3', A_202))), inference(superposition, [status(thm), theory('equality')], [c_1588, c_1819])).
% 3.91/1.72  tff(c_1874, plain, (![B_175]: (k2_xboole_0('#skF_3', B_175)=B_175 | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_1551, c_1866])).
% 3.91/1.72  tff(c_1900, plain, (![B_203]: (k2_xboole_0('#skF_3', B_203)=B_203)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1874])).
% 3.91/1.72  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.91/1.72  tff(c_1914, plain, (![B_203]: (k4_xboole_0(B_203, B_203)=k4_xboole_0('#skF_3', B_203))), inference(superposition, [status(thm), theory('equality')], [c_1900, c_26])).
% 3.91/1.72  tff(c_1932, plain, (![B_203]: (k4_xboole_0(B_203, B_203)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1914])).
% 3.91/1.72  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.91/1.72  tff(c_1582, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k4_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1553])).
% 3.91/1.72  tff(c_2032, plain, (![A_14]: (k5_xboole_0(A_14, A_14)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1932, c_1582])).
% 3.91/1.72  tff(c_2168, plain, (![A_211, B_212, C_213]: (k5_xboole_0(k5_xboole_0(A_211, B_212), C_213)=k5_xboole_0(A_211, k5_xboole_0(B_212, C_213)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.91/1.72  tff(c_2212, plain, (![A_14, C_213]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_213))=k5_xboole_0('#skF_3', C_213))), inference(superposition, [status(thm), theory('equality')], [c_2032, c_2168])).
% 3.91/1.72  tff(c_2273, plain, (![A_214, C_215]: (k5_xboole_0(A_214, k5_xboole_0(A_214, C_215))=C_215)), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_2212])).
% 3.91/1.72  tff(c_2328, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2273])).
% 3.91/1.72  tff(c_2347, plain, (![A_216, B_217]: (k5_xboole_0(A_216, k5_xboole_0(B_217, A_216))=B_217)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2273])).
% 3.91/1.72  tff(c_2377, plain, (![B_4, A_3]: (k5_xboole_0(k5_xboole_0(B_4, A_3), B_4)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_2328, c_2347])).
% 3.91/1.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.91/1.72  tff(c_1251, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_66])).
% 3.91/1.72  tff(c_1572, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1553])).
% 3.91/1.72  tff(c_36, plain, (![A_30, B_31]: (k5_xboole_0(k5_xboole_0(A_30, B_31), k3_xboole_0(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.91/1.72  tff(c_2222, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k5_xboole_0(B_31, k3_xboole_0(A_30, B_31)))=k2_xboole_0(A_30, B_31))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2168])).
% 3.91/1.72  tff(c_2680, plain, (![A_226, B_227]: (k5_xboole_0(A_226, k4_xboole_0(B_227, A_226))=k2_xboole_0(A_226, B_227))), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_2222])).
% 3.91/1.72  tff(c_2267, plain, (![A_14, C_213]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_213))=C_213)), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_2212])).
% 3.91/1.72  tff(c_2975, plain, (![A_252, B_253]: (k5_xboole_0(A_252, k2_xboole_0(A_252, B_253))=k4_xboole_0(B_253, A_252))), inference(superposition, [status(thm), theory('equality')], [c_2680, c_2267])).
% 3.91/1.72  tff(c_3033, plain, (k5_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1251, c_2975])).
% 3.91/1.72  tff(c_3043, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2032, c_3033])).
% 3.91/1.72  tff(c_2315, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k4_xboole_0(B_2, A_1))=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_1572, c_2273])).
% 3.91/1.72  tff(c_3047, plain, (k5_xboole_0('#skF_6', '#skF_3')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3043, c_2315])).
% 3.91/1.72  tff(c_3059, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_111, c_3047])).
% 3.91/1.72  tff(c_3080, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_5'), '#skF_6')=k2_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3059, c_36])).
% 3.91/1.72  tff(c_3089, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2377, c_3080])).
% 3.91/1.72  tff(c_32, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.91/1.72  tff(c_3140, plain, (r1_tarski('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3089, c_32])).
% 3.91/1.72  tff(c_1777, plain, (![B_196, A_197]: (k1_tarski(B_196)=A_197 | A_197='#skF_3' | ~r1_tarski(A_197, k1_tarski(B_196)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_52])).
% 3.91/1.72  tff(c_1788, plain, (![A_197]: (k1_tarski('#skF_4')=A_197 | A_197='#skF_3' | ~r1_tarski(A_197, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1250, c_1777])).
% 3.91/1.72  tff(c_1795, plain, (![A_197]: (A_197='#skF_5' | A_197='#skF_3' | ~r1_tarski(A_197, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_1788])).
% 3.91/1.72  tff(c_3148, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_3140, c_1795])).
% 3.91/1.72  tff(c_3152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1249, c_1278, c_3148])).
% 3.91/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.72  
% 3.91/1.72  Inference rules
% 3.91/1.72  ----------------------
% 3.91/1.72  #Ref     : 0
% 3.91/1.72  #Sup     : 729
% 3.91/1.72  #Fact    : 0
% 3.91/1.72  #Define  : 0
% 3.91/1.72  #Split   : 3
% 3.91/1.72  #Chain   : 0
% 3.91/1.72  #Close   : 0
% 3.91/1.72  
% 3.91/1.72  Ordering : KBO
% 3.91/1.72  
% 3.91/1.72  Simplification rules
% 3.91/1.72  ----------------------
% 3.91/1.72  #Subsume      : 15
% 3.91/1.72  #Demod        : 411
% 3.91/1.72  #Tautology    : 534
% 3.91/1.72  #SimpNegUnit  : 8
% 3.91/1.72  #BackRed      : 18
% 3.91/1.72  
% 3.91/1.72  #Partial instantiations: 0
% 3.91/1.72  #Strategies tried      : 1
% 3.91/1.72  
% 3.91/1.72  Timing (in seconds)
% 3.91/1.72  ----------------------
% 3.91/1.73  Preprocessing        : 0.34
% 3.91/1.73  Parsing              : 0.18
% 3.91/1.73  CNF conversion       : 0.02
% 3.91/1.73  Main loop            : 0.60
% 3.91/1.73  Inferencing          : 0.21
% 3.91/1.73  Reduction            : 0.23
% 3.91/1.73  Demodulation         : 0.18
% 3.91/1.73  BG Simplification    : 0.03
% 3.91/1.73  Subsumption          : 0.08
% 3.91/1.73  Abstraction          : 0.03
% 3.91/1.73  MUC search           : 0.00
% 3.91/1.73  Cooper               : 0.00
% 3.91/1.73  Total                : 0.99
% 3.91/1.73  Index Insertion      : 0.00
% 3.91/1.73  Index Deletion       : 0.00
% 3.91/1.73  Index Matching       : 0.00
% 3.91/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
