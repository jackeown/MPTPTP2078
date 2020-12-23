%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:16 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 400 expanded)
%              Number of leaves         :   31 ( 142 expanded)
%              Depth                    :   13
%              Number of atoms          :  179 ( 889 expanded)
%              Number of equality atoms :   62 ( 476 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_54,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_69,plain,(
    ! [A_43,B_44] : r1_tarski(A_43,k2_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_69])).

tff(c_1420,plain,(
    ! [B_196,A_197] :
      ( B_196 = A_197
      | ~ r1_tarski(B_196,A_197)
      | ~ r1_tarski(A_197,B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1426,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_1420])).

tff(c_1435,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1426])).

tff(c_1477,plain,(
    ! [A_208,B_209] :
      ( r2_hidden('#skF_2'(A_208,B_209),A_208)
      | r1_tarski(A_208,B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1731,plain,(
    ! [A_240,B_241] :
      ( '#skF_2'(k1_tarski(A_240),B_241) = A_240
      | r1_tarski(k1_tarski(A_240),B_241) ) ),
    inference(resolution,[status(thm)],[c_1477,c_26])).

tff(c_1752,plain,(
    '#skF_2'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1731,c_1435])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1759,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1752,c_8])).

tff(c_1765,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1435,c_1759])).

tff(c_412,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_tarski(B_99,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_418,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_412])).

tff(c_427,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_418])).

tff(c_433,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_2'(A_101,B_102),A_101)
      | r1_tarski(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_760,plain,(
    ! [A_139,B_140] :
      ( '#skF_2'(k1_tarski(A_139),B_140) = A_139
      | r1_tarski(k1_tarski(A_139),B_140) ) ),
    inference(resolution,[status(thm)],[c_433,c_26])).

tff(c_790,plain,(
    '#skF_2'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_760,c_427])).

tff(c_798,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_8])).

tff(c_804,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_798])).

tff(c_56,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_87,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_601,plain,(
    ! [C_119,B_120,A_121] :
      ( r2_hidden(C_119,B_120)
      | ~ r2_hidden(C_119,A_121)
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_641,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_1'(A_125),B_126)
      | ~ r1_tarski(A_125,B_126)
      | v1_xboole_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_4,c_601])).

tff(c_1115,plain,(
    ! [A_162,A_163] :
      ( A_162 = '#skF_1'(A_163)
      | ~ r1_tarski(A_163,k1_tarski(A_162))
      | v1_xboole_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_641,c_26])).

tff(c_1146,plain,
    ( '#skF_1'('#skF_7') = '#skF_6'
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_1115])).

tff(c_1150,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1146])).

tff(c_121,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_3'(A_53),A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_1157,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1150,c_130])).

tff(c_1163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1157])).

tff(c_1165,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1146])).

tff(c_1164,plain,(
    '#skF_1'('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1146])).

tff(c_1197,plain,
    ( v1_xboole_0('#skF_7')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_4])).

tff(c_1202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_804,c_1165,c_1197])).

tff(c_1203,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1700,plain,(
    ! [C_237,B_238,A_239] :
      ( r2_hidden(C_237,B_238)
      | ~ r2_hidden(C_237,A_239)
      | ~ r1_tarski(A_239,B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1919,plain,(
    ! [A_248,B_249] :
      ( r2_hidden('#skF_1'(A_248),B_249)
      | ~ r1_tarski(A_248,B_249)
      | v1_xboole_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_4,c_1700])).

tff(c_2210,plain,(
    ! [A_279,A_280] :
      ( A_279 = '#skF_1'(A_280)
      | ~ r1_tarski(A_280,k1_tarski(A_279))
      | v1_xboole_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_1919,c_26])).

tff(c_2241,plain,
    ( '#skF_1'('#skF_7') = '#skF_6'
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_2210])).

tff(c_2245,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2241])).

tff(c_1487,plain,(
    ! [A_210,B_211] :
      ( ~ v1_xboole_0(A_210)
      | r1_tarski(A_210,B_211) ) ),
    inference(resolution,[status(thm)],[c_1477,c_2])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1512,plain,(
    ! [A_210,B_211] :
      ( k2_xboole_0(A_210,B_211) = B_211
      | ~ v1_xboole_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_1487,c_22])).

tff(c_2254,plain,(
    ! [B_211] : k2_xboole_0('#skF_7',B_211) = B_211 ),
    inference(resolution,[status(thm)],[c_2245,c_1512])).

tff(c_2283,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2254,c_60])).

tff(c_2285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1203,c_2283])).

tff(c_2287,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2241])).

tff(c_2286,plain,(
    '#skF_1'('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2241])).

tff(c_2294,plain,
    ( v1_xboole_0('#skF_7')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2286,c_4])).

tff(c_2299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1765,c_2287,c_2294])).

tff(c_2301,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2343,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_2301,c_58])).

tff(c_18,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2309,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_60])).

tff(c_2681,plain,(
    ! [A_330,C_331,B_332] :
      ( r1_tarski(A_330,k2_xboole_0(C_331,B_332))
      | ~ r1_tarski(A_330,B_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2710,plain,(
    ! [A_333] :
      ( r1_tarski(A_333,'#skF_7')
      | ~ r1_tarski(A_333,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2309,c_2681])).

tff(c_2763,plain,(
    ! [A_341] :
      ( k2_xboole_0(A_341,'#skF_7') = '#skF_7'
      | ~ r1_tarski(A_341,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2710,c_22])).

tff(c_2773,plain,(
    k2_xboole_0('#skF_8','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_18,c_2763])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2780,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2773,c_24])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2785,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_2780,c_14])).

tff(c_2791,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2343,c_2785])).

tff(c_2562,plain,(
    ! [A_315,B_316] :
      ( r2_hidden('#skF_2'(A_315,B_316),A_315)
      | r1_tarski(A_315,B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2344,plain,(
    ! [C_288,A_289] :
      ( C_288 = A_289
      | ~ r2_hidden(C_288,k1_tarski(A_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2347,plain,(
    ! [C_288] :
      ( C_288 = '#skF_6'
      | ~ r2_hidden(C_288,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2301,c_2344])).

tff(c_2798,plain,(
    ! [B_342] :
      ( '#skF_2'('#skF_7',B_342) = '#skF_6'
      | r1_tarski('#skF_7',B_342) ) ),
    inference(resolution,[status(thm)],[c_2562,c_2347])).

tff(c_2817,plain,(
    '#skF_2'('#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2798,c_2791])).

tff(c_2956,plain,(
    ! [A_361,B_362] :
      ( ~ r2_hidden('#skF_2'(A_361,B_362),B_362)
      | r1_tarski(A_361,B_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2962,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r1_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2817,c_2956])).

tff(c_2967,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2791,c_2962])).

tff(c_2300,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3176,plain,(
    ! [C_372,B_373,A_374] :
      ( r2_hidden(C_372,B_373)
      | ~ r2_hidden(C_372,A_374)
      | ~ r1_tarski(A_374,B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3538,plain,(
    ! [A_403,B_404] :
      ( r2_hidden('#skF_1'(A_403),B_404)
      | ~ r1_tarski(A_403,B_404)
      | v1_xboole_0(A_403) ) ),
    inference(resolution,[status(thm)],[c_4,c_3176])).

tff(c_3600,plain,(
    ! [A_407] :
      ( '#skF_1'(A_407) = '#skF_6'
      | ~ r1_tarski(A_407,'#skF_7')
      | v1_xboole_0(A_407) ) ),
    inference(resolution,[status(thm)],[c_3538,c_2347])).

tff(c_3629,plain,
    ( '#skF_1'('#skF_8') = '#skF_6'
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2780,c_3600])).

tff(c_3635,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3629])).

tff(c_2359,plain,(
    ! [A_291] :
      ( r2_hidden('#skF_3'(A_291),A_291)
      | k1_xboole_0 = A_291 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2375,plain,(
    ! [A_291] :
      ( ~ v1_xboole_0(A_291)
      | k1_xboole_0 = A_291 ) ),
    inference(resolution,[status(thm)],[c_2359,c_2])).

tff(c_3645,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3635,c_2375])).

tff(c_3653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2300,c_3645])).

tff(c_3655,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3629])).

tff(c_3654,plain,(
    '#skF_1'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3629])).

tff(c_3662,plain,
    ( v1_xboole_0('#skF_8')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3654,c_4])).

tff(c_3667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2967,c_3655,c_3662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:34:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.84  
% 4.58/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.84  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 4.58/1.84  
% 4.58/1.84  %Foreground sorts:
% 4.58/1.84  
% 4.58/1.84  
% 4.58/1.84  %Background operators:
% 4.58/1.84  
% 4.58/1.84  
% 4.58/1.84  %Foreground operators:
% 4.58/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.58/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.58/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.58/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.58/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.58/1.84  tff('#skF_7', type, '#skF_7': $i).
% 4.58/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.58/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.58/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.58/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.58/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.58/1.84  tff('#skF_8', type, '#skF_8': $i).
% 4.58/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.58/1.84  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.58/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.58/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.58/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.58/1.84  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.58/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.58/1.84  
% 4.58/1.86  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.58/1.86  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.58/1.86  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.58/1.86  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.58/1.86  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.58/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.58/1.86  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.58/1.86  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.58/1.86  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.58/1.86  tff(c_54, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_64, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_54])).
% 4.58/1.86  tff(c_60, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_69, plain, (![A_43, B_44]: (r1_tarski(A_43, k2_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.58/1.86  tff(c_72, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_69])).
% 4.58/1.86  tff(c_1420, plain, (![B_196, A_197]: (B_196=A_197 | ~r1_tarski(B_196, A_197) | ~r1_tarski(A_197, B_196))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.58/1.86  tff(c_1426, plain, (k1_tarski('#skF_6')='#skF_7' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_72, c_1420])).
% 4.58/1.86  tff(c_1435, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_1426])).
% 4.58/1.86  tff(c_1477, plain, (![A_208, B_209]: (r2_hidden('#skF_2'(A_208, B_209), A_208) | r1_tarski(A_208, B_209))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.58/1.86  tff(c_26, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.58/1.86  tff(c_1731, plain, (![A_240, B_241]: ('#skF_2'(k1_tarski(A_240), B_241)=A_240 | r1_tarski(k1_tarski(A_240), B_241))), inference(resolution, [status(thm)], [c_1477, c_26])).
% 4.58/1.86  tff(c_1752, plain, ('#skF_2'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1731, c_1435])).
% 4.58/1.86  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.58/1.86  tff(c_1759, plain, (~r2_hidden('#skF_6', '#skF_7') | r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1752, c_8])).
% 4.58/1.86  tff(c_1765, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1435, c_1759])).
% 4.58/1.86  tff(c_412, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_tarski(B_99, A_100) | ~r1_tarski(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.58/1.86  tff(c_418, plain, (k1_tarski('#skF_6')='#skF_7' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_72, c_412])).
% 4.58/1.86  tff(c_427, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_418])).
% 4.58/1.86  tff(c_433, plain, (![A_101, B_102]: (r2_hidden('#skF_2'(A_101, B_102), A_101) | r1_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.58/1.86  tff(c_760, plain, (![A_139, B_140]: ('#skF_2'(k1_tarski(A_139), B_140)=A_139 | r1_tarski(k1_tarski(A_139), B_140))), inference(resolution, [status(thm)], [c_433, c_26])).
% 4.58/1.86  tff(c_790, plain, ('#skF_2'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_760, c_427])).
% 4.58/1.86  tff(c_798, plain, (~r2_hidden('#skF_6', '#skF_7') | r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_790, c_8])).
% 4.58/1.86  tff(c_804, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_427, c_798])).
% 4.58/1.86  tff(c_56, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_87, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_56])).
% 4.58/1.86  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.86  tff(c_601, plain, (![C_119, B_120, A_121]: (r2_hidden(C_119, B_120) | ~r2_hidden(C_119, A_121) | ~r1_tarski(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.58/1.86  tff(c_641, plain, (![A_125, B_126]: (r2_hidden('#skF_1'(A_125), B_126) | ~r1_tarski(A_125, B_126) | v1_xboole_0(A_125))), inference(resolution, [status(thm)], [c_4, c_601])).
% 4.58/1.86  tff(c_1115, plain, (![A_162, A_163]: (A_162='#skF_1'(A_163) | ~r1_tarski(A_163, k1_tarski(A_162)) | v1_xboole_0(A_163))), inference(resolution, [status(thm)], [c_641, c_26])).
% 4.58/1.86  tff(c_1146, plain, ('#skF_1'('#skF_7')='#skF_6' | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_72, c_1115])).
% 4.58/1.86  tff(c_1150, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1146])).
% 4.58/1.86  tff(c_121, plain, (![A_53]: (r2_hidden('#skF_3'(A_53), A_53) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.58/1.86  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.86  tff(c_130, plain, (![A_53]: (~v1_xboole_0(A_53) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_121, c_2])).
% 4.58/1.86  tff(c_1157, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1150, c_130])).
% 4.58/1.86  tff(c_1163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_1157])).
% 4.58/1.86  tff(c_1165, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1146])).
% 4.58/1.86  tff(c_1164, plain, ('#skF_1'('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_1146])).
% 4.58/1.86  tff(c_1197, plain, (v1_xboole_0('#skF_7') | r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1164, c_4])).
% 4.58/1.86  tff(c_1202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_804, c_1165, c_1197])).
% 4.58/1.86  tff(c_1203, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_56])).
% 4.58/1.86  tff(c_1700, plain, (![C_237, B_238, A_239]: (r2_hidden(C_237, B_238) | ~r2_hidden(C_237, A_239) | ~r1_tarski(A_239, B_238))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.58/1.86  tff(c_1919, plain, (![A_248, B_249]: (r2_hidden('#skF_1'(A_248), B_249) | ~r1_tarski(A_248, B_249) | v1_xboole_0(A_248))), inference(resolution, [status(thm)], [c_4, c_1700])).
% 4.58/1.86  tff(c_2210, plain, (![A_279, A_280]: (A_279='#skF_1'(A_280) | ~r1_tarski(A_280, k1_tarski(A_279)) | v1_xboole_0(A_280))), inference(resolution, [status(thm)], [c_1919, c_26])).
% 4.58/1.86  tff(c_2241, plain, ('#skF_1'('#skF_7')='#skF_6' | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_72, c_2210])).
% 4.58/1.86  tff(c_2245, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_2241])).
% 4.58/1.86  tff(c_1487, plain, (![A_210, B_211]: (~v1_xboole_0(A_210) | r1_tarski(A_210, B_211))), inference(resolution, [status(thm)], [c_1477, c_2])).
% 4.58/1.86  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.58/1.86  tff(c_1512, plain, (![A_210, B_211]: (k2_xboole_0(A_210, B_211)=B_211 | ~v1_xboole_0(A_210))), inference(resolution, [status(thm)], [c_1487, c_22])).
% 4.58/1.86  tff(c_2254, plain, (![B_211]: (k2_xboole_0('#skF_7', B_211)=B_211)), inference(resolution, [status(thm)], [c_2245, c_1512])).
% 4.58/1.86  tff(c_2283, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2254, c_60])).
% 4.58/1.86  tff(c_2285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1203, c_2283])).
% 4.58/1.86  tff(c_2287, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_2241])).
% 4.58/1.86  tff(c_2286, plain, ('#skF_1'('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_2241])).
% 4.58/1.86  tff(c_2294, plain, (v1_xboole_0('#skF_7') | r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2286, c_4])).
% 4.58/1.86  tff(c_2299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1765, c_2287, c_2294])).
% 4.58/1.86  tff(c_2301, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_54])).
% 4.58/1.86  tff(c_58, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_2343, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_2301, c_58])).
% 4.58/1.86  tff(c_18, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.58/1.86  tff(c_2309, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_60])).
% 4.58/1.86  tff(c_2681, plain, (![A_330, C_331, B_332]: (r1_tarski(A_330, k2_xboole_0(C_331, B_332)) | ~r1_tarski(A_330, B_332))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.58/1.86  tff(c_2710, plain, (![A_333]: (r1_tarski(A_333, '#skF_7') | ~r1_tarski(A_333, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2309, c_2681])).
% 4.58/1.86  tff(c_2763, plain, (![A_341]: (k2_xboole_0(A_341, '#skF_7')='#skF_7' | ~r1_tarski(A_341, '#skF_8'))), inference(resolution, [status(thm)], [c_2710, c_22])).
% 4.58/1.86  tff(c_2773, plain, (k2_xboole_0('#skF_8', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_18, c_2763])).
% 4.58/1.86  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.58/1.86  tff(c_2780, plain, (r1_tarski('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2773, c_24])).
% 4.58/1.86  tff(c_14, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.58/1.86  tff(c_2785, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_2780, c_14])).
% 4.58/1.86  tff(c_2791, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2343, c_2785])).
% 4.58/1.86  tff(c_2562, plain, (![A_315, B_316]: (r2_hidden('#skF_2'(A_315, B_316), A_315) | r1_tarski(A_315, B_316))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.58/1.86  tff(c_2344, plain, (![C_288, A_289]: (C_288=A_289 | ~r2_hidden(C_288, k1_tarski(A_289)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.58/1.86  tff(c_2347, plain, (![C_288]: (C_288='#skF_6' | ~r2_hidden(C_288, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2301, c_2344])).
% 4.58/1.86  tff(c_2798, plain, (![B_342]: ('#skF_2'('#skF_7', B_342)='#skF_6' | r1_tarski('#skF_7', B_342))), inference(resolution, [status(thm)], [c_2562, c_2347])).
% 4.58/1.86  tff(c_2817, plain, ('#skF_2'('#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_2798, c_2791])).
% 4.58/1.86  tff(c_2956, plain, (![A_361, B_362]: (~r2_hidden('#skF_2'(A_361, B_362), B_362) | r1_tarski(A_361, B_362))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.58/1.86  tff(c_2962, plain, (~r2_hidden('#skF_6', '#skF_8') | r1_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2817, c_2956])).
% 4.58/1.86  tff(c_2967, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2791, c_2962])).
% 4.58/1.86  tff(c_2300, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 4.58/1.86  tff(c_3176, plain, (![C_372, B_373, A_374]: (r2_hidden(C_372, B_373) | ~r2_hidden(C_372, A_374) | ~r1_tarski(A_374, B_373))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.58/1.86  tff(c_3538, plain, (![A_403, B_404]: (r2_hidden('#skF_1'(A_403), B_404) | ~r1_tarski(A_403, B_404) | v1_xboole_0(A_403))), inference(resolution, [status(thm)], [c_4, c_3176])).
% 4.58/1.86  tff(c_3600, plain, (![A_407]: ('#skF_1'(A_407)='#skF_6' | ~r1_tarski(A_407, '#skF_7') | v1_xboole_0(A_407))), inference(resolution, [status(thm)], [c_3538, c_2347])).
% 4.58/1.86  tff(c_3629, plain, ('#skF_1'('#skF_8')='#skF_6' | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_2780, c_3600])).
% 4.58/1.86  tff(c_3635, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_3629])).
% 4.58/1.86  tff(c_2359, plain, (![A_291]: (r2_hidden('#skF_3'(A_291), A_291) | k1_xboole_0=A_291)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.58/1.86  tff(c_2375, plain, (![A_291]: (~v1_xboole_0(A_291) | k1_xboole_0=A_291)), inference(resolution, [status(thm)], [c_2359, c_2])).
% 4.58/1.86  tff(c_3645, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_3635, c_2375])).
% 4.58/1.86  tff(c_3653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2300, c_3645])).
% 4.58/1.86  tff(c_3655, plain, (~v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_3629])).
% 4.58/1.86  tff(c_3654, plain, ('#skF_1'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_3629])).
% 4.58/1.86  tff(c_3662, plain, (v1_xboole_0('#skF_8') | r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3654, c_4])).
% 4.58/1.86  tff(c_3667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2967, c_3655, c_3662])).
% 4.58/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.86  
% 4.58/1.86  Inference rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Ref     : 0
% 4.58/1.86  #Sup     : 844
% 4.58/1.86  #Fact    : 0
% 4.58/1.86  #Define  : 0
% 4.58/1.86  #Split   : 6
% 4.58/1.86  #Chain   : 0
% 4.58/1.86  #Close   : 0
% 4.58/1.86  
% 4.58/1.86  Ordering : KBO
% 4.58/1.86  
% 4.58/1.86  Simplification rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Subsume      : 242
% 4.58/1.86  #Demod        : 188
% 4.58/1.86  #Tautology    : 318
% 4.58/1.86  #SimpNegUnit  : 74
% 4.58/1.86  #BackRed      : 3
% 4.58/1.86  
% 4.58/1.86  #Partial instantiations: 0
% 4.58/1.86  #Strategies tried      : 1
% 4.58/1.86  
% 4.58/1.86  Timing (in seconds)
% 4.58/1.86  ----------------------
% 4.58/1.86  Preprocessing        : 0.33
% 4.58/1.86  Parsing              : 0.17
% 4.58/1.86  CNF conversion       : 0.03
% 4.58/1.86  Main loop            : 0.74
% 4.58/1.86  Inferencing          : 0.29
% 4.58/1.86  Reduction            : 0.22
% 4.58/1.86  Demodulation         : 0.15
% 4.58/1.86  BG Simplification    : 0.03
% 4.58/1.86  Subsumption          : 0.14
% 4.58/1.86  Abstraction          : 0.04
% 4.58/1.86  MUC search           : 0.00
% 4.58/1.86  Cooper               : 0.00
% 4.58/1.86  Total                : 1.11
% 4.58/1.86  Index Insertion      : 0.00
% 4.58/1.86  Index Deletion       : 0.00
% 4.58/1.86  Index Matching       : 0.00
% 4.58/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
