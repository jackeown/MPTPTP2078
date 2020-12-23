%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:13 EST 2020

% Result     : Theorem 18.89s
% Output     : CNFRefutation 18.89s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 320 expanded)
%              Number of leaves         :   44 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  192 ( 583 expanded)
%              Number of equality atoms :  107 ( 448 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_68,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_76,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_149,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_66,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_tarski(A_65),B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_74,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_150,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_30])).

tff(c_461,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ r1_tarski(B_115,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_475,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_145,c_461])).

tff(c_488,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_475])).

tff(c_497,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_488])).

tff(c_14,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_403,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(k1_tarski(A_105),B_106)
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_411,plain,(
    ! [A_105,B_106] :
      ( k2_xboole_0(k1_tarski(A_105),B_106) = B_106
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_403,c_24])).

tff(c_391,plain,(
    ! [A_103,B_104] :
      ( r2_hidden(A_103,B_104)
      | ~ r1_tarski(k1_tarski(A_103),B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_400,plain,(
    ! [A_103,B_25] : r2_hidden(A_103,k2_xboole_0(k1_tarski(A_103),B_25)) ),
    inference(resolution,[status(thm)],[c_30,c_391])).

tff(c_716,plain,(
    ! [C_135,B_136,A_137] :
      ( r2_hidden(C_135,B_136)
      | ~ r2_hidden(C_135,A_137)
      | ~ r1_tarski(A_137,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_874,plain,(
    ! [A_152,B_153,B_154] :
      ( r2_hidden(A_152,B_153)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_152),B_154),B_153) ) ),
    inference(resolution,[status(thm)],[c_400,c_716])).

tff(c_1142,plain,(
    ! [A_161,B_162,B_163] : r2_hidden(A_161,k2_xboole_0(k2_xboole_0(k1_tarski(A_161),B_162),B_163)) ),
    inference(resolution,[status(thm)],[c_30,c_874])).

tff(c_1234,plain,(
    ! [A_166,B_167,B_168] :
      ( r2_hidden(A_166,k2_xboole_0(B_167,B_168))
      | ~ r2_hidden(A_166,B_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_1142])).

tff(c_1564,plain,(
    ! [A_176] :
      ( r2_hidden(A_176,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_176,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1234])).

tff(c_38,plain,(
    ! [C_36,A_32] :
      ( C_36 = A_32
      | ~ r2_hidden(C_36,k1_tarski(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1577,plain,(
    ! [A_177] :
      ( A_177 = '#skF_5'
      | ~ r2_hidden(A_177,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1564,c_38])).

tff(c_1589,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_14,c_1577])).

tff(c_1594,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_1589])).

tff(c_1601,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1594,c_14])).

tff(c_1606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_497,c_1601])).

tff(c_1608,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1643,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1608,c_1608,c_78])).

tff(c_1610,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1608,c_80])).

tff(c_1607,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1644,plain,(
    ! [B_181,A_182] : k5_xboole_0(B_181,A_182) = k5_xboole_0(A_182,B_181) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1660,plain,(
    ! [A_182] : k5_xboole_0(k1_xboole_0,A_182) = A_182 ),
    inference(superposition,[status(thm),theory(equality)],[c_1644,c_28])).

tff(c_34,plain,(
    ! [A_29] : k5_xboole_0(A_29,A_29) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2853,plain,(
    ! [A_264,B_265,C_266] : k5_xboole_0(k5_xboole_0(A_264,B_265),C_266) = k5_xboole_0(A_264,k5_xboole_0(B_265,C_266)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2957,plain,(
    ! [A_29,C_266] : k5_xboole_0(A_29,k5_xboole_0(A_29,C_266)) = k5_xboole_0(k1_xboole_0,C_266) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2853])).

tff(c_2978,plain,(
    ! [A_29,C_266] : k5_xboole_0(A_29,k5_xboole_0(A_29,C_266)) = C_266 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1660,c_2957])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2578,plain,(
    ! [A_256,B_257] : k5_xboole_0(k5_xboole_0(A_256,B_257),k2_xboole_0(A_256,B_257)) = k3_xboole_0(A_256,B_257) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2632,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_6') = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1610,c_2578])).

tff(c_2714,plain,(
    k5_xboole_0('#skF_6',k5_xboole_0('#skF_6','#skF_7')) = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2632])).

tff(c_2981,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2978,c_2714])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1835,plain,(
    ! [A_195,B_196,C_197] : r1_tarski(k3_xboole_0(A_195,B_196),k2_xboole_0(A_195,C_197)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1841,plain,(
    ! [A_8,B_196] : r1_tarski(k3_xboole_0(A_8,B_196),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1835])).

tff(c_3078,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2981,c_1841])).

tff(c_2098,plain,(
    ! [C_226,B_227,A_228] :
      ( r2_hidden(C_226,B_227)
      | ~ r2_hidden(C_226,A_228)
      | ~ r1_tarski(A_228,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6355,plain,(
    ! [A_12203,B_12204] :
      ( r2_hidden('#skF_2'(A_12203),B_12204)
      | ~ r1_tarski(A_12203,B_12204)
      | k1_xboole_0 = A_12203 ) ),
    inference(resolution,[status(thm)],[c_14,c_2098])).

tff(c_1627,plain,(
    ! [C_178,A_179] :
      ( C_178 = A_179
      | ~ r2_hidden(C_178,k1_tarski(A_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1630,plain,(
    ! [C_178] :
      ( C_178 = '#skF_5'
      | ~ r2_hidden(C_178,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_1627])).

tff(c_6383,plain,(
    ! [A_12257] :
      ( '#skF_2'(A_12257) = '#skF_5'
      | ~ r1_tarski(A_12257,'#skF_6')
      | k1_xboole_0 = A_12257 ) ),
    inference(resolution,[status(thm)],[c_6355,c_1630])).

tff(c_6413,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3078,c_6383])).

tff(c_6453,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1607,c_6413])).

tff(c_6474,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_6453,c_14])).

tff(c_6478,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1607,c_6474])).

tff(c_1870,plain,(
    ! [A_202,B_203] :
      ( r1_tarski(k1_tarski(A_202),B_203)
      | ~ r2_hidden(A_202,B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2289,plain,(
    ! [A_239,B_240] :
      ( k2_xboole_0(k1_tarski(A_239),B_240) = B_240
      | ~ r2_hidden(A_239,B_240) ) ),
    inference(resolution,[status(thm)],[c_1870,c_24])).

tff(c_2322,plain,(
    ! [B_240] :
      ( k2_xboole_0('#skF_6',B_240) = B_240
      | ~ r2_hidden('#skF_5',B_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_2289])).

tff(c_6482,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6478,c_2322])).

tff(c_6489,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1610,c_6482])).

tff(c_6491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1643,c_6489])).

tff(c_6492,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_6493,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_6495,plain,(
    ! [A_29] : k5_xboole_0(A_29,A_29) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6493,c_34])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6823,plain,(
    ! [A_12449,B_12450] : k5_xboole_0(A_12449,k3_xboole_0(A_12449,B_12450)) = k4_xboole_0(A_12449,B_12450) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6840,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6823])).

tff(c_6843,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6495,c_6840])).

tff(c_70,plain,(
    ! [B_70] : k4_xboole_0(k1_tarski(B_70),k1_tarski(B_70)) != k1_tarski(B_70) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6844,plain,(
    ! [B_70] : k1_tarski(B_70) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6843,c_70])).

tff(c_72,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(k1_tarski(A_69),k1_tarski(B_70)) = k1_tarski(A_69)
      | B_70 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6527,plain,(
    ! [B_12416,A_12417] : k5_xboole_0(B_12416,A_12417) = k5_xboole_0(A_12417,B_12416) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6496,plain,(
    ! [A_23] : k5_xboole_0(A_23,'#skF_6') = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6493,c_28])).

tff(c_6543,plain,(
    ! [A_12417] : k5_xboole_0('#skF_6',A_12417) = A_12417 ),
    inference(superposition,[status(thm),theory(equality)],[c_6527,c_6496])).

tff(c_7203,plain,(
    ! [A_12484,B_12485,C_12486] : k5_xboole_0(k5_xboole_0(A_12484,B_12485),C_12486) = k5_xboole_0(A_12484,k5_xboole_0(B_12485,C_12486)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7267,plain,(
    ! [A_29,C_12486] : k5_xboole_0(A_29,k5_xboole_0(A_29,C_12486)) = k5_xboole_0('#skF_6',C_12486) ),
    inference(superposition,[status(thm),theory(equality)],[c_6495,c_7203])).

tff(c_7281,plain,(
    ! [A_12487,C_12488] : k5_xboole_0(A_12487,k5_xboole_0(A_12487,C_12488)) = C_12488 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6543,c_7267])).

tff(c_9989,plain,(
    ! [A_16464,B_16465] : k5_xboole_0(A_16464,k4_xboole_0(A_16464,B_16465)) = k3_xboole_0(A_16464,B_16465) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_7281])).

tff(c_10042,plain,(
    ! [A_69,B_70] :
      ( k5_xboole_0(k1_tarski(A_69),k1_tarski(A_69)) = k3_xboole_0(k1_tarski(A_69),k1_tarski(B_70))
      | B_70 = A_69 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_9989])).

tff(c_10536,plain,(
    ! [A_17050,B_17051] :
      ( k3_xboole_0(k1_tarski(A_17050),k1_tarski(B_17051)) = '#skF_6'
      | B_17051 = A_17050 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6495,c_10042])).

tff(c_6682,plain,(
    ! [A_12428,B_12429,C_12430] : r1_tarski(k3_xboole_0(A_12428,B_12429),k2_xboole_0(A_12428,C_12430)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6694,plain,(
    ! [A_8,B_12429] : r1_tarski(k3_xboole_0(A_8,B_12429),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6682])).

tff(c_35631,plain,(
    ! [XT_25227,B_17105] :
      ( r1_tarski('#skF_6',k1_tarski(k1_tarski(XT_25227)))
      | k1_tarski(XT_25227) = B_17105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10536,c_6694])).

tff(c_35633,plain,(
    ! [XT_25227] :
      ( k1_tarski(XT_25227) = '#skF_6'
      | r1_tarski('#skF_6',k1_tarski(k1_tarski(XT_25227))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35631,c_6495])).

tff(c_39731,plain,(
    ! [XT_27825] : r1_tarski('#skF_6',k1_tarski(k1_tarski(XT_27825))) ),
    inference(negUnitSimplification,[status(thm)],[c_6844,c_35633])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39733,plain,(
    ! [XT_27825] :
      ( k1_tarski(k1_tarski(XT_27825)) = '#skF_6'
      | ~ r1_tarski(k1_tarski(k1_tarski(XT_27825)),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_39731,c_16])).

tff(c_40548,plain,(
    ! [XT_28144] : ~ r1_tarski(k1_tarski(k1_tarski(XT_28144)),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_6844,c_39733])).

tff(c_40580,plain,(
    ! [XT_28144] : ~ r2_hidden(k1_tarski(XT_28144),'#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_40548])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10697,plain,(
    ! [A_17104,B_17105] :
      ( r1_tarski('#skF_6',k1_tarski(A_17104))
      | B_17105 = A_17104 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10536,c_6694])).

tff(c_10699,plain,(
    ! [A_17104,B_17105] :
      ( k1_tarski(A_17104) = '#skF_6'
      | ~ r1_tarski(k1_tarski(A_17104),'#skF_6')
      | B_17105 = A_17104 ) ),
    inference(resolution,[status(thm)],[c_10697,c_16])).

tff(c_41707,plain,(
    ! [A_28933,B_28934] :
      ( ~ r1_tarski(k1_tarski(A_28933),'#skF_6')
      | B_28934 = A_28933 ) ),
    inference(negUnitSimplification,[status(thm)],[c_6844,c_10699])).

tff(c_41730,plain,(
    ! [B_29091,A_29092] :
      ( B_29091 = A_29092
      | ~ r2_hidden(A_29092,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_41707])).

tff(c_135242,plain,(
    ! [XT_65802,B_61112] :
      ( k1_tarski(XT_65802) = '#skF_1'('#skF_6',B_61112)
      | r1_tarski('#skF_6',B_61112) ) ),
    inference(resolution,[status(thm)],[c_8,c_41730])).

tff(c_135245,plain,(
    ! [XT_65802,B_61112] :
      ( r2_hidden(k1_tarski(XT_65802),'#skF_6')
      | r1_tarski('#skF_6',B_61112)
      | r1_tarski('#skF_6',B_61112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135242,c_8])).

tff(c_135983,plain,(
    ! [B_61112] :
      ( r1_tarski('#skF_6',B_61112)
      | r1_tarski('#skF_6',B_61112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40580,c_135245])).

tff(c_136184,plain,(
    ! [B_68498] : r1_tarski('#skF_6',B_68498) ),
    inference(factorization,[status(thm),theory(equality)],[c_135983])).

tff(c_136233,plain,(
    ! [B_68498] : k2_xboole_0('#skF_6',B_68498) = B_68498 ),
    inference(resolution,[status(thm)],[c_136184,c_24])).

tff(c_136239,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136233,c_80])).

tff(c_136242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6492,c_136239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.89/9.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.89/9.64  
% 18.89/9.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.89/9.64  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 18.89/9.64  
% 18.89/9.64  %Foreground sorts:
% 18.89/9.64  
% 18.89/9.64  
% 18.89/9.64  %Background operators:
% 18.89/9.64  
% 18.89/9.64  
% 18.89/9.64  %Foreground operators:
% 18.89/9.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 18.89/9.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.89/9.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.89/9.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.89/9.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.89/9.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.89/9.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.89/9.64  tff('#skF_7', type, '#skF_7': $i).
% 18.89/9.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.89/9.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.89/9.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.89/9.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.89/9.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.89/9.64  tff('#skF_5', type, '#skF_5': $i).
% 18.89/9.64  tff('#skF_6', type, '#skF_6': $i).
% 18.89/9.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.89/9.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.89/9.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.89/9.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.89/9.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.89/9.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.89/9.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.89/9.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.89/9.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.89/9.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.89/9.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 18.89/9.64  
% 18.89/9.66  tff(f_121, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 18.89/9.66  tff(f_95, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 18.89/9.66  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.89/9.66  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.89/9.66  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 18.89/9.66  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.89/9.66  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 18.89/9.66  tff(f_77, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 18.89/9.66  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 18.89/9.66  tff(f_62, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 18.89/9.66  tff(f_68, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 18.89/9.66  tff(f_66, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 18.89/9.66  tff(f_70, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 18.89/9.66  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 18.89/9.66  tff(f_60, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 18.89/9.66  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 18.89/9.66  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 18.89/9.66  tff(f_102, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 18.89/9.66  tff(c_76, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 18.89/9.66  tff(c_149, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_76])).
% 18.89/9.66  tff(c_66, plain, (![A_65, B_66]: (r1_tarski(k1_tarski(A_65), B_66) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.89/9.66  tff(c_74, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 18.89/9.66  tff(c_150, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_74])).
% 18.89/9.66  tff(c_80, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 18.89/9.66  tff(c_30, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 18.89/9.66  tff(c_145, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_30])).
% 18.89/9.66  tff(c_461, plain, (![B_115, A_116]: (B_115=A_116 | ~r1_tarski(B_115, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.89/9.66  tff(c_475, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_145, c_461])).
% 18.89/9.66  tff(c_488, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_150, c_475])).
% 18.89/9.66  tff(c_497, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_488])).
% 18.89/9.66  tff(c_14, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 18.89/9.66  tff(c_403, plain, (![A_105, B_106]: (r1_tarski(k1_tarski(A_105), B_106) | ~r2_hidden(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.89/9.66  tff(c_24, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.89/9.66  tff(c_411, plain, (![A_105, B_106]: (k2_xboole_0(k1_tarski(A_105), B_106)=B_106 | ~r2_hidden(A_105, B_106))), inference(resolution, [status(thm)], [c_403, c_24])).
% 18.89/9.66  tff(c_391, plain, (![A_103, B_104]: (r2_hidden(A_103, B_104) | ~r1_tarski(k1_tarski(A_103), B_104))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.89/9.66  tff(c_400, plain, (![A_103, B_25]: (r2_hidden(A_103, k2_xboole_0(k1_tarski(A_103), B_25)))), inference(resolution, [status(thm)], [c_30, c_391])).
% 18.89/9.66  tff(c_716, plain, (![C_135, B_136, A_137]: (r2_hidden(C_135, B_136) | ~r2_hidden(C_135, A_137) | ~r1_tarski(A_137, B_136))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.89/9.66  tff(c_874, plain, (![A_152, B_153, B_154]: (r2_hidden(A_152, B_153) | ~r1_tarski(k2_xboole_0(k1_tarski(A_152), B_154), B_153))), inference(resolution, [status(thm)], [c_400, c_716])).
% 18.89/9.66  tff(c_1142, plain, (![A_161, B_162, B_163]: (r2_hidden(A_161, k2_xboole_0(k2_xboole_0(k1_tarski(A_161), B_162), B_163)))), inference(resolution, [status(thm)], [c_30, c_874])).
% 18.89/9.66  tff(c_1234, plain, (![A_166, B_167, B_168]: (r2_hidden(A_166, k2_xboole_0(B_167, B_168)) | ~r2_hidden(A_166, B_167))), inference(superposition, [status(thm), theory('equality')], [c_411, c_1142])).
% 18.89/9.66  tff(c_1564, plain, (![A_176]: (r2_hidden(A_176, k1_tarski('#skF_5')) | ~r2_hidden(A_176, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_1234])).
% 18.89/9.66  tff(c_38, plain, (![C_36, A_32]: (C_36=A_32 | ~r2_hidden(C_36, k1_tarski(A_32)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.89/9.66  tff(c_1577, plain, (![A_177]: (A_177='#skF_5' | ~r2_hidden(A_177, '#skF_6'))), inference(resolution, [status(thm)], [c_1564, c_38])).
% 18.89/9.66  tff(c_1589, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_14, c_1577])).
% 18.89/9.66  tff(c_1594, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_149, c_1589])).
% 18.89/9.66  tff(c_1601, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1594, c_14])).
% 18.89/9.66  tff(c_1606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_497, c_1601])).
% 18.89/9.66  tff(c_1608, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 18.89/9.66  tff(c_78, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 18.89/9.66  tff(c_1643, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1608, c_1608, c_78])).
% 18.89/9.66  tff(c_1610, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1608, c_80])).
% 18.89/9.66  tff(c_1607, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 18.89/9.66  tff(c_1644, plain, (![B_181, A_182]: (k5_xboole_0(B_181, A_182)=k5_xboole_0(A_182, B_181))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.89/9.66  tff(c_28, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.89/9.66  tff(c_1660, plain, (![A_182]: (k5_xboole_0(k1_xboole_0, A_182)=A_182)), inference(superposition, [status(thm), theory('equality')], [c_1644, c_28])).
% 18.89/9.66  tff(c_34, plain, (![A_29]: (k5_xboole_0(A_29, A_29)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.89/9.66  tff(c_2853, plain, (![A_264, B_265, C_266]: (k5_xboole_0(k5_xboole_0(A_264, B_265), C_266)=k5_xboole_0(A_264, k5_xboole_0(B_265, C_266)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.89/9.66  tff(c_2957, plain, (![A_29, C_266]: (k5_xboole_0(A_29, k5_xboole_0(A_29, C_266))=k5_xboole_0(k1_xboole_0, C_266))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2853])).
% 18.89/9.66  tff(c_2978, plain, (![A_29, C_266]: (k5_xboole_0(A_29, k5_xboole_0(A_29, C_266))=C_266)), inference(demodulation, [status(thm), theory('equality')], [c_1660, c_2957])).
% 18.89/9.66  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.89/9.66  tff(c_2578, plain, (![A_256, B_257]: (k5_xboole_0(k5_xboole_0(A_256, B_257), k2_xboole_0(A_256, B_257))=k3_xboole_0(A_256, B_257))), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.89/9.66  tff(c_2632, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_6')=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1610, c_2578])).
% 18.89/9.66  tff(c_2714, plain, (k5_xboole_0('#skF_6', k5_xboole_0('#skF_6', '#skF_7'))=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2, c_2632])).
% 18.89/9.66  tff(c_2981, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2978, c_2714])).
% 18.89/9.66  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 18.89/9.66  tff(c_1835, plain, (![A_195, B_196, C_197]: (r1_tarski(k3_xboole_0(A_195, B_196), k2_xboole_0(A_195, C_197)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.89/9.66  tff(c_1841, plain, (![A_8, B_196]: (r1_tarski(k3_xboole_0(A_8, B_196), A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1835])).
% 18.89/9.66  tff(c_3078, plain, (r1_tarski('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2981, c_1841])).
% 18.89/9.66  tff(c_2098, plain, (![C_226, B_227, A_228]: (r2_hidden(C_226, B_227) | ~r2_hidden(C_226, A_228) | ~r1_tarski(A_228, B_227))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.89/9.66  tff(c_6355, plain, (![A_12203, B_12204]: (r2_hidden('#skF_2'(A_12203), B_12204) | ~r1_tarski(A_12203, B_12204) | k1_xboole_0=A_12203)), inference(resolution, [status(thm)], [c_14, c_2098])).
% 18.89/9.66  tff(c_1627, plain, (![C_178, A_179]: (C_178=A_179 | ~r2_hidden(C_178, k1_tarski(A_179)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.89/9.66  tff(c_1630, plain, (![C_178]: (C_178='#skF_5' | ~r2_hidden(C_178, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1608, c_1627])).
% 18.89/9.66  tff(c_6383, plain, (![A_12257]: ('#skF_2'(A_12257)='#skF_5' | ~r1_tarski(A_12257, '#skF_6') | k1_xboole_0=A_12257)), inference(resolution, [status(thm)], [c_6355, c_1630])).
% 18.89/9.66  tff(c_6413, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_3078, c_6383])).
% 18.89/9.66  tff(c_6453, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1607, c_6413])).
% 18.89/9.66  tff(c_6474, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_6453, c_14])).
% 18.89/9.66  tff(c_6478, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1607, c_6474])).
% 18.89/9.66  tff(c_1870, plain, (![A_202, B_203]: (r1_tarski(k1_tarski(A_202), B_203) | ~r2_hidden(A_202, B_203))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.89/9.66  tff(c_2289, plain, (![A_239, B_240]: (k2_xboole_0(k1_tarski(A_239), B_240)=B_240 | ~r2_hidden(A_239, B_240))), inference(resolution, [status(thm)], [c_1870, c_24])).
% 18.89/9.66  tff(c_2322, plain, (![B_240]: (k2_xboole_0('#skF_6', B_240)=B_240 | ~r2_hidden('#skF_5', B_240))), inference(superposition, [status(thm), theory('equality')], [c_1608, c_2289])).
% 18.89/9.66  tff(c_6482, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_6478, c_2322])).
% 18.89/9.66  tff(c_6489, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1610, c_6482])).
% 18.89/9.66  tff(c_6491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1643, c_6489])).
% 18.89/9.66  tff(c_6492, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 18.89/9.66  tff(c_6493, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_76])).
% 18.89/9.66  tff(c_6495, plain, (![A_29]: (k5_xboole_0(A_29, A_29)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6493, c_34])).
% 18.89/9.66  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.89/9.66  tff(c_6823, plain, (![A_12449, B_12450]: (k5_xboole_0(A_12449, k3_xboole_0(A_12449, B_12450))=k4_xboole_0(A_12449, B_12450))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.89/9.66  tff(c_6840, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6823])).
% 18.89/9.66  tff(c_6843, plain, (![A_10]: (k4_xboole_0(A_10, A_10)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6495, c_6840])).
% 18.89/9.66  tff(c_70, plain, (![B_70]: (k4_xboole_0(k1_tarski(B_70), k1_tarski(B_70))!=k1_tarski(B_70))), inference(cnfTransformation, [status(thm)], [f_102])).
% 18.89/9.66  tff(c_6844, plain, (![B_70]: (k1_tarski(B_70)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6843, c_70])).
% 18.89/9.66  tff(c_72, plain, (![A_69, B_70]: (k4_xboole_0(k1_tarski(A_69), k1_tarski(B_70))=k1_tarski(A_69) | B_70=A_69)), inference(cnfTransformation, [status(thm)], [f_102])).
% 18.89/9.66  tff(c_22, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.89/9.66  tff(c_6527, plain, (![B_12416, A_12417]: (k5_xboole_0(B_12416, A_12417)=k5_xboole_0(A_12417, B_12416))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.89/9.66  tff(c_6496, plain, (![A_23]: (k5_xboole_0(A_23, '#skF_6')=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_6493, c_28])).
% 18.89/9.66  tff(c_6543, plain, (![A_12417]: (k5_xboole_0('#skF_6', A_12417)=A_12417)), inference(superposition, [status(thm), theory('equality')], [c_6527, c_6496])).
% 18.89/9.66  tff(c_7203, plain, (![A_12484, B_12485, C_12486]: (k5_xboole_0(k5_xboole_0(A_12484, B_12485), C_12486)=k5_xboole_0(A_12484, k5_xboole_0(B_12485, C_12486)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.89/9.66  tff(c_7267, plain, (![A_29, C_12486]: (k5_xboole_0(A_29, k5_xboole_0(A_29, C_12486))=k5_xboole_0('#skF_6', C_12486))), inference(superposition, [status(thm), theory('equality')], [c_6495, c_7203])).
% 18.89/9.66  tff(c_7281, plain, (![A_12487, C_12488]: (k5_xboole_0(A_12487, k5_xboole_0(A_12487, C_12488))=C_12488)), inference(demodulation, [status(thm), theory('equality')], [c_6543, c_7267])).
% 18.89/9.66  tff(c_9989, plain, (![A_16464, B_16465]: (k5_xboole_0(A_16464, k4_xboole_0(A_16464, B_16465))=k3_xboole_0(A_16464, B_16465))), inference(superposition, [status(thm), theory('equality')], [c_22, c_7281])).
% 18.89/9.66  tff(c_10042, plain, (![A_69, B_70]: (k5_xboole_0(k1_tarski(A_69), k1_tarski(A_69))=k3_xboole_0(k1_tarski(A_69), k1_tarski(B_70)) | B_70=A_69)), inference(superposition, [status(thm), theory('equality')], [c_72, c_9989])).
% 18.89/9.66  tff(c_10536, plain, (![A_17050, B_17051]: (k3_xboole_0(k1_tarski(A_17050), k1_tarski(B_17051))='#skF_6' | B_17051=A_17050)), inference(demodulation, [status(thm), theory('equality')], [c_6495, c_10042])).
% 18.89/9.66  tff(c_6682, plain, (![A_12428, B_12429, C_12430]: (r1_tarski(k3_xboole_0(A_12428, B_12429), k2_xboole_0(A_12428, C_12430)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.89/9.66  tff(c_6694, plain, (![A_8, B_12429]: (r1_tarski(k3_xboole_0(A_8, B_12429), A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_6682])).
% 18.89/9.66  tff(c_35631, plain, (![XT_25227, B_17105]: (r1_tarski('#skF_6', k1_tarski(k1_tarski(XT_25227))) | k1_tarski(XT_25227)=B_17105)), inference(superposition, [status(thm), theory('equality')], [c_10536, c_6694])).
% 18.89/9.66  tff(c_35633, plain, (![XT_25227]: (k1_tarski(XT_25227)='#skF_6' | r1_tarski('#skF_6', k1_tarski(k1_tarski(XT_25227))))), inference(superposition, [status(thm), theory('equality')], [c_35631, c_6495])).
% 18.89/9.66  tff(c_39731, plain, (![XT_27825]: (r1_tarski('#skF_6', k1_tarski(k1_tarski(XT_27825))))), inference(negUnitSimplification, [status(thm)], [c_6844, c_35633])).
% 18.89/9.66  tff(c_16, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.89/9.66  tff(c_39733, plain, (![XT_27825]: (k1_tarski(k1_tarski(XT_27825))='#skF_6' | ~r1_tarski(k1_tarski(k1_tarski(XT_27825)), '#skF_6'))), inference(resolution, [status(thm)], [c_39731, c_16])).
% 18.89/9.66  tff(c_40548, plain, (![XT_28144]: (~r1_tarski(k1_tarski(k1_tarski(XT_28144)), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_6844, c_39733])).
% 18.89/9.66  tff(c_40580, plain, (![XT_28144]: (~r2_hidden(k1_tarski(XT_28144), '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_40548])).
% 18.89/9.66  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.89/9.66  tff(c_10697, plain, (![A_17104, B_17105]: (r1_tarski('#skF_6', k1_tarski(A_17104)) | B_17105=A_17104)), inference(superposition, [status(thm), theory('equality')], [c_10536, c_6694])).
% 18.89/9.66  tff(c_10699, plain, (![A_17104, B_17105]: (k1_tarski(A_17104)='#skF_6' | ~r1_tarski(k1_tarski(A_17104), '#skF_6') | B_17105=A_17104)), inference(resolution, [status(thm)], [c_10697, c_16])).
% 18.89/9.66  tff(c_41707, plain, (![A_28933, B_28934]: (~r1_tarski(k1_tarski(A_28933), '#skF_6') | B_28934=A_28933)), inference(negUnitSimplification, [status(thm)], [c_6844, c_10699])).
% 18.89/9.66  tff(c_41730, plain, (![B_29091, A_29092]: (B_29091=A_29092 | ~r2_hidden(A_29092, '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_41707])).
% 18.89/9.66  tff(c_135242, plain, (![XT_65802, B_61112]: (k1_tarski(XT_65802)='#skF_1'('#skF_6', B_61112) | r1_tarski('#skF_6', B_61112))), inference(resolution, [status(thm)], [c_8, c_41730])).
% 18.89/9.66  tff(c_135245, plain, (![XT_65802, B_61112]: (r2_hidden(k1_tarski(XT_65802), '#skF_6') | r1_tarski('#skF_6', B_61112) | r1_tarski('#skF_6', B_61112))), inference(superposition, [status(thm), theory('equality')], [c_135242, c_8])).
% 18.89/9.66  tff(c_135983, plain, (![B_61112]: (r1_tarski('#skF_6', B_61112) | r1_tarski('#skF_6', B_61112))), inference(negUnitSimplification, [status(thm)], [c_40580, c_135245])).
% 18.89/9.66  tff(c_136184, plain, (![B_68498]: (r1_tarski('#skF_6', B_68498))), inference(factorization, [status(thm), theory('equality')], [c_135983])).
% 18.89/9.66  tff(c_136233, plain, (![B_68498]: (k2_xboole_0('#skF_6', B_68498)=B_68498)), inference(resolution, [status(thm)], [c_136184, c_24])).
% 18.89/9.66  tff(c_136239, plain, (k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_136233, c_80])).
% 18.89/9.66  tff(c_136242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6492, c_136239])).
% 18.89/9.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.89/9.66  
% 18.89/9.66  Inference rules
% 18.89/9.66  ----------------------
% 18.89/9.66  #Ref     : 0
% 18.89/9.66  #Sup     : 20890
% 18.89/9.66  #Fact    : 6
% 18.89/9.66  #Define  : 0
% 18.89/9.66  #Split   : 11
% 18.89/9.66  #Chain   : 0
% 18.89/9.66  #Close   : 0
% 18.89/9.66  
% 18.89/9.66  Ordering : KBO
% 18.89/9.66  
% 18.89/9.66  Simplification rules
% 18.89/9.66  ----------------------
% 18.89/9.66  #Subsume      : 6259
% 18.89/9.66  #Demod        : 10895
% 18.89/9.66  #Tautology    : 4195
% 18.89/9.66  #SimpNegUnit  : 245
% 18.89/9.66  #BackRed      : 19
% 18.89/9.66  
% 18.89/9.66  #Partial instantiations: 25509
% 18.89/9.66  #Strategies tried      : 1
% 18.89/9.66  
% 18.89/9.66  Timing (in seconds)
% 18.89/9.66  ----------------------
% 18.89/9.67  Preprocessing        : 0.34
% 18.89/9.67  Parsing              : 0.18
% 18.89/9.67  CNF conversion       : 0.03
% 18.89/9.67  Main loop            : 8.54
% 18.89/9.67  Inferencing          : 2.18
% 18.89/9.67  Reduction            : 4.13
% 18.89/9.67  Demodulation         : 3.30
% 18.89/9.67  BG Simplification    : 0.29
% 18.89/9.67  Subsumption          : 1.53
% 18.89/9.67  Abstraction          : 0.41
% 18.89/9.67  MUC search           : 0.00
% 18.89/9.67  Cooper               : 0.00
% 18.89/9.67  Total                : 8.93
% 18.89/9.67  Index Insertion      : 0.00
% 18.89/9.67  Index Deletion       : 0.00
% 18.89/9.67  Index Matching       : 0.00
% 18.89/9.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
