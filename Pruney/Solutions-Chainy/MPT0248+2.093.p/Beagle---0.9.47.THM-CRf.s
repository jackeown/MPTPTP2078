%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:17 EST 2020

% Result     : Theorem 6.44s
% Output     : CNFRefutation 6.44s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 475 expanded)
%              Number of leaves         :   43 ( 173 expanded)
%              Depth                    :   18
%              Number of atoms          :  193 ( 810 expanded)
%              Number of equality atoms :  101 ( 656 expanded)
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

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_82,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_138,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_80,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_137,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_86,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_129,plain,(
    ! [A_77,B_78] : r1_tarski(A_77,k2_xboole_0(A_77,B_78)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_132,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_129])).

tff(c_343,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ r1_tarski(B_111,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_347,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_132,c_343])).

tff(c_357,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_347])).

tff(c_235,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93),A_92)
      | r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_569,plain,(
    ! [A_137,B_138] :
      ( '#skF_1'(k1_tarski(A_137),B_138) = A_137
      | r1_tarski(k1_tarski(A_137),B_138) ) ),
    inference(resolution,[status(thm)],[c_235,c_46])).

tff(c_591,plain,(
    '#skF_1'(k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_569,c_357])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_598,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_4])).

tff(c_604,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_598])).

tff(c_24,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_507,plain,(
    ! [C_127,B_128,A_129] :
      ( r2_hidden(C_127,B_128)
      | ~ r2_hidden(C_127,A_129)
      | ~ r1_tarski(A_129,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_541,plain,(
    ! [A_133,B_134] :
      ( r2_hidden('#skF_2'(A_133),B_134)
      | ~ r1_tarski(A_133,B_134)
      | k1_xboole_0 = A_133 ) ),
    inference(resolution,[status(thm)],[c_24,c_507])).

tff(c_688,plain,(
    ! [A_144,A_145] :
      ( A_144 = '#skF_2'(A_145)
      | ~ r1_tarski(A_145,k1_tarski(A_144))
      | k1_xboole_0 = A_145 ) ),
    inference(resolution,[status(thm)],[c_541,c_46])).

tff(c_699,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_132,c_688])).

tff(c_713,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_699])).

tff(c_761,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_24])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_604,c_761])).

tff(c_767,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_768,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_42,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_769,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_42])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_985,plain,(
    ! [A_189,B_190] : k5_xboole_0(A_189,k3_xboole_0(A_189,B_190)) = k4_xboole_0(A_189,B_190) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_994,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_985])).

tff(c_998,plain,(
    ! [A_191] : k4_xboole_0(A_191,A_191) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_994])).

tff(c_36,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_794,plain,(
    ! [A_153,B_154] :
      ( k2_xboole_0(A_153,B_154) = B_154
      | ~ r1_tarski(A_153,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_809,plain,(
    ! [A_21,B_22] : k2_xboole_0(k4_xboole_0(A_21,B_22),A_21) = A_21 ),
    inference(resolution,[status(thm)],[c_36,c_794])).

tff(c_1003,plain,(
    ! [A_191] : k2_xboole_0('#skF_6',A_191) = A_191 ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_809])).

tff(c_1046,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_86])).

tff(c_1048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_767,c_1046])).

tff(c_1050,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_84,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1107,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1050,c_84])).

tff(c_1052,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_86])).

tff(c_1049,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1160,plain,(
    ! [A_207,B_208] :
      ( r2_hidden('#skF_1'(A_207,B_208),A_207)
      | r1_tarski(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1069,plain,(
    ! [C_196,A_197] :
      ( C_196 = A_197
      | ~ r2_hidden(C_196,k1_tarski(A_197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1072,plain,(
    ! [C_196] :
      ( C_196 = '#skF_5'
      | ~ r2_hidden(C_196,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_1069])).

tff(c_1203,plain,(
    ! [B_212] :
      ( '#skF_1'('#skF_6',B_212) = '#skF_5'
      | r1_tarski('#skF_6',B_212) ) ),
    inference(resolution,[status(thm)],[c_1160,c_1072])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1209,plain,(
    ! [B_213] :
      ( k2_xboole_0('#skF_6',B_213) = B_213
      | '#skF_1'('#skF_6',B_213) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1203,c_34])).

tff(c_1215,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_1052])).

tff(c_1234,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1107,c_1215])).

tff(c_1283,plain,(
    ! [A_221,B_222] :
      ( ~ r2_hidden('#skF_1'(A_221,B_222),B_222)
      | r1_tarski(A_221,B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1286,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1234,c_1283])).

tff(c_1293,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1286])).

tff(c_30,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1912,plain,(
    ! [A_274,B_275] : k5_xboole_0(k5_xboole_0(A_274,B_275),k2_xboole_0(A_274,B_275)) = k3_xboole_0(A_274,B_275) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1945,plain,(
    ! [A_6] : k5_xboole_0(k5_xboole_0(A_6,A_6),A_6) = k3_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1912])).

tff(c_1951,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10,c_1945])).

tff(c_2070,plain,(
    ! [A_282,B_283,C_284] : k5_xboole_0(k5_xboole_0(A_282,B_283),C_284) = k5_xboole_0(A_282,k5_xboole_0(B_283,C_284)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2125,plain,(
    ! [A_28,C_284] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_284)) = k5_xboole_0(k1_xboole_0,C_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2070])).

tff(c_2136,plain,(
    ! [A_285,C_286] : k5_xboole_0(A_285,k5_xboole_0(A_285,C_286)) = C_286 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1951,c_2125])).

tff(c_2188,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2136])).

tff(c_2249,plain,(
    ! [A_288,B_289] : k5_xboole_0(A_288,k5_xboole_0(B_289,k5_xboole_0(A_288,B_289))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2070,c_42])).

tff(c_2135,plain,(
    ! [A_28,C_284] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_284)) = C_284 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1951,c_2125])).

tff(c_2257,plain,(
    ! [B_289,A_288] : k5_xboole_0(B_289,k5_xboole_0(A_288,B_289)) = k5_xboole_0(A_288,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2249,c_2135])).

tff(c_2331,plain,(
    ! [B_289,A_288] : k5_xboole_0(B_289,k5_xboole_0(A_288,B_289)) = A_288 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2188,c_2257])).

tff(c_1942,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_6') = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_1912])).

tff(c_2079,plain,(
    k5_xboole_0('#skF_6',k5_xboole_0('#skF_7','#skF_6')) = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2070,c_1942])).

tff(c_2371,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2331,c_2079])).

tff(c_32,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2459,plain,(
    k5_xboole_0('#skF_6','#skF_7') = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2371,c_32])).

tff(c_2455,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_1942])).

tff(c_2469,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2455,c_2135])).

tff(c_2817,plain,(
    k5_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_2469])).

tff(c_58,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1264,plain,(
    ! [B_216,C_217,A_218] :
      ( r2_hidden(B_216,C_217)
      | ~ r1_tarski(k2_tarski(A_218,B_216),C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1341,plain,(
    ! [A_230,C_231] :
      ( r2_hidden(A_230,C_231)
      | ~ r1_tarski(k1_tarski(A_230),C_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1264])).

tff(c_1344,plain,(
    ! [C_231] :
      ( r2_hidden('#skF_5',C_231)
      | ~ r1_tarski('#skF_6',C_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_1341])).

tff(c_2567,plain,(
    ! [A_294,B_295,C_296] :
      ( r2_hidden(A_294,B_295)
      | r2_hidden(A_294,C_296)
      | ~ r2_hidden(A_294,k5_xboole_0(B_295,C_296)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3266,plain,(
    ! [B_307,C_308] :
      ( r2_hidden('#skF_5',B_307)
      | r2_hidden('#skF_5',C_308)
      | ~ r1_tarski('#skF_6',k5_xboole_0(B_307,C_308)) ) ),
    inference(resolution,[status(thm)],[c_1344,c_2567])).

tff(c_3284,plain,
    ( r2_hidden('#skF_5',k4_xboole_0('#skF_6','#skF_7'))
    | r2_hidden('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2817,c_3266])).

tff(c_3332,plain,
    ( r2_hidden('#skF_5',k4_xboole_0('#skF_6','#skF_7'))
    | r2_hidden('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3284])).

tff(c_3333,plain,(
    r2_hidden('#skF_5',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_1293,c_3332])).

tff(c_3179,plain,(
    ! [A_304,B_305,C_306] :
      ( r1_tarski(k2_tarski(A_304,B_305),C_306)
      | ~ r2_hidden(B_305,C_306)
      | ~ r2_hidden(A_304,C_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7574,plain,(
    ! [A_8222,C_8223] :
      ( r1_tarski(k1_tarski(A_8222),C_8223)
      | ~ r2_hidden(A_8222,C_8223)
      | ~ r2_hidden(A_8222,C_8223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_3179])).

tff(c_7676,plain,(
    ! [A_8276,C_8277] :
      ( k2_xboole_0(k1_tarski(A_8276),C_8277) = C_8277
      | ~ r2_hidden(A_8276,C_8277) ) ),
    inference(resolution,[status(thm)],[c_7574,c_34])).

tff(c_38,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7828,plain,(
    ! [A_8330,C_8331] :
      ( r1_tarski(k1_tarski(A_8330),C_8331)
      | ~ r2_hidden(A_8330,C_8331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7676,c_38])).

tff(c_7930,plain,(
    ! [C_8384] :
      ( r1_tarski('#skF_6',C_8384)
      | ~ r2_hidden('#skF_5',C_8384) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_7828])).

tff(c_7995,plain,(
    r1_tarski('#skF_6',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_3333,c_7930])).

tff(c_1248,plain,(
    ! [B_214,A_215] :
      ( B_214 = A_215
      | ~ r1_tarski(B_214,A_215)
      | ~ r1_tarski(A_215,B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1259,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,k4_xboole_0(A_21,B_22)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1248])).

tff(c_8151,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7995,c_1259])).

tff(c_44,plain,(
    ! [A_29,B_30] : k5_xboole_0(k5_xboole_0(A_29,B_30),k2_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6546,plain,(
    ! [A_7684,B_7685] : k5_xboole_0(A_7684,k5_xboole_0(B_7685,k2_xboole_0(A_7684,B_7685))) = k3_xboole_0(A_7684,B_7685) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2070])).

tff(c_6587,plain,(
    ! [B_7685,A_7684] : k5_xboole_0(B_7685,k2_xboole_0(A_7684,B_7685)) = k5_xboole_0(A_7684,k3_xboole_0(A_7684,B_7685)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6546,c_2135])).

tff(c_6830,plain,(
    ! [B_7846,A_7847] : k5_xboole_0(B_7846,k2_xboole_0(A_7847,B_7846)) = k4_xboole_0(A_7847,B_7846) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6587])).

tff(c_7023,plain,(
    ! [B_7954,A_7955] : k5_xboole_0(B_7954,k4_xboole_0(A_7955,B_7954)) = k2_xboole_0(A_7955,B_7954) ),
    inference(superposition,[status(thm),theory(equality)],[c_6830,c_2135])).

tff(c_7064,plain,(
    ! [A_7955,B_7954] : k5_xboole_0(k4_xboole_0(A_7955,B_7954),k2_xboole_0(A_7955,B_7954)) = B_7954 ),
    inference(superposition,[status(thm),theory(equality)],[c_7023,c_2331])).

tff(c_8184,plain,(
    k5_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_8151,c_7064])).

tff(c_8234,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1052,c_8184])).

tff(c_8236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1049,c_8234])).

tff(c_8237,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1286])).

tff(c_8243,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_8237,c_34])).

tff(c_8248,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_8243])).

tff(c_8250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1107,c_8248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:36:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.44/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.44/2.35  
% 6.44/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.44/2.36  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 6.44/2.36  
% 6.44/2.36  %Foreground sorts:
% 6.44/2.36  
% 6.44/2.36  
% 6.44/2.36  %Background operators:
% 6.44/2.36  
% 6.44/2.36  
% 6.44/2.36  %Foreground operators:
% 6.44/2.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.44/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.44/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.44/2.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.44/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.44/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.44/2.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.44/2.36  tff('#skF_7', type, '#skF_7': $i).
% 6.44/2.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.44/2.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.44/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.44/2.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.44/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.44/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.44/2.36  tff('#skF_6', type, '#skF_6': $i).
% 6.44/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.44/2.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.44/2.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.44/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.44/2.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.44/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.44/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.44/2.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.44/2.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.44/2.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.44/2.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.44/2.36  
% 6.44/2.38  tff(f_121, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.44/2.38  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.44/2.38  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.44/2.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.44/2.38  tff(f_80, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.44/2.38  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.44/2.38  tff(f_71, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.44/2.38  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.44/2.38  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.44/2.38  tff(f_65, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.44/2.38  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.44/2.38  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.44/2.38  tff(f_73, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.44/2.38  tff(f_69, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.44/2.38  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.44/2.38  tff(f_102, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.44/2.38  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.44/2.38  tff(c_82, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.44/2.38  tff(c_138, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_82])).
% 6.44/2.38  tff(c_80, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.44/2.38  tff(c_137, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_80])).
% 6.44/2.38  tff(c_86, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.44/2.38  tff(c_129, plain, (![A_77, B_78]: (r1_tarski(A_77, k2_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.44/2.38  tff(c_132, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_129])).
% 6.44/2.38  tff(c_343, plain, (![B_111, A_112]: (B_111=A_112 | ~r1_tarski(B_111, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.44/2.38  tff(c_347, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_132, c_343])).
% 6.44/2.38  tff(c_357, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_137, c_347])).
% 6.44/2.38  tff(c_235, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93), A_92) | r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.44/2.38  tff(c_46, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.44/2.38  tff(c_569, plain, (![A_137, B_138]: ('#skF_1'(k1_tarski(A_137), B_138)=A_137 | r1_tarski(k1_tarski(A_137), B_138))), inference(resolution, [status(thm)], [c_235, c_46])).
% 6.44/2.38  tff(c_591, plain, ('#skF_1'(k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_569, c_357])).
% 6.44/2.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.44/2.38  tff(c_598, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_591, c_4])).
% 6.44/2.38  tff(c_604, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_357, c_598])).
% 6.44/2.38  tff(c_24, plain, (![A_13]: (r2_hidden('#skF_2'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.44/2.38  tff(c_507, plain, (![C_127, B_128, A_129]: (r2_hidden(C_127, B_128) | ~r2_hidden(C_127, A_129) | ~r1_tarski(A_129, B_128))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.44/2.38  tff(c_541, plain, (![A_133, B_134]: (r2_hidden('#skF_2'(A_133), B_134) | ~r1_tarski(A_133, B_134) | k1_xboole_0=A_133)), inference(resolution, [status(thm)], [c_24, c_507])).
% 6.44/2.38  tff(c_688, plain, (![A_144, A_145]: (A_144='#skF_2'(A_145) | ~r1_tarski(A_145, k1_tarski(A_144)) | k1_xboole_0=A_145)), inference(resolution, [status(thm)], [c_541, c_46])).
% 6.44/2.38  tff(c_699, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_132, c_688])).
% 6.44/2.38  tff(c_713, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_138, c_699])).
% 6.44/2.38  tff(c_761, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_713, c_24])).
% 6.44/2.38  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_604, c_761])).
% 6.44/2.38  tff(c_767, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_82])).
% 6.44/2.38  tff(c_768, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_82])).
% 6.44/2.38  tff(c_42, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.44/2.38  tff(c_769, plain, (![A_28]: (k5_xboole_0(A_28, A_28)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_768, c_42])).
% 6.44/2.38  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.44/2.38  tff(c_985, plain, (![A_189, B_190]: (k5_xboole_0(A_189, k3_xboole_0(A_189, B_190))=k4_xboole_0(A_189, B_190))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.44/2.38  tff(c_994, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_985])).
% 6.44/2.38  tff(c_998, plain, (![A_191]: (k4_xboole_0(A_191, A_191)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_769, c_994])).
% 6.44/2.38  tff(c_36, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.44/2.38  tff(c_794, plain, (![A_153, B_154]: (k2_xboole_0(A_153, B_154)=B_154 | ~r1_tarski(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.44/2.38  tff(c_809, plain, (![A_21, B_22]: (k2_xboole_0(k4_xboole_0(A_21, B_22), A_21)=A_21)), inference(resolution, [status(thm)], [c_36, c_794])).
% 6.44/2.38  tff(c_1003, plain, (![A_191]: (k2_xboole_0('#skF_6', A_191)=A_191)), inference(superposition, [status(thm), theory('equality')], [c_998, c_809])).
% 6.44/2.38  tff(c_1046, plain, (k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1003, c_86])).
% 6.44/2.38  tff(c_1048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_767, c_1046])).
% 6.44/2.38  tff(c_1050, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_80])).
% 6.44/2.38  tff(c_84, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.44/2.38  tff(c_1107, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1050, c_84])).
% 6.44/2.38  tff(c_1052, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_86])).
% 6.44/2.38  tff(c_1049, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 6.44/2.38  tff(c_1160, plain, (![A_207, B_208]: (r2_hidden('#skF_1'(A_207, B_208), A_207) | r1_tarski(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.44/2.38  tff(c_1069, plain, (![C_196, A_197]: (C_196=A_197 | ~r2_hidden(C_196, k1_tarski(A_197)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.44/2.38  tff(c_1072, plain, (![C_196]: (C_196='#skF_5' | ~r2_hidden(C_196, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_1069])).
% 6.44/2.38  tff(c_1203, plain, (![B_212]: ('#skF_1'('#skF_6', B_212)='#skF_5' | r1_tarski('#skF_6', B_212))), inference(resolution, [status(thm)], [c_1160, c_1072])).
% 6.44/2.38  tff(c_34, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.44/2.38  tff(c_1209, plain, (![B_213]: (k2_xboole_0('#skF_6', B_213)=B_213 | '#skF_1'('#skF_6', B_213)='#skF_5')), inference(resolution, [status(thm)], [c_1203, c_34])).
% 6.44/2.38  tff(c_1215, plain, ('#skF_7'='#skF_6' | '#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1209, c_1052])).
% 6.44/2.38  tff(c_1234, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1107, c_1215])).
% 6.44/2.38  tff(c_1283, plain, (![A_221, B_222]: (~r2_hidden('#skF_1'(A_221, B_222), B_222) | r1_tarski(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.44/2.38  tff(c_1286, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1234, c_1283])).
% 6.44/2.38  tff(c_1293, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_1286])).
% 6.44/2.38  tff(c_30, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.44/2.38  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.44/2.38  tff(c_1912, plain, (![A_274, B_275]: (k5_xboole_0(k5_xboole_0(A_274, B_275), k2_xboole_0(A_274, B_275))=k3_xboole_0(A_274, B_275))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.44/2.38  tff(c_1945, plain, (![A_6]: (k5_xboole_0(k5_xboole_0(A_6, A_6), A_6)=k3_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1912])).
% 6.44/2.38  tff(c_1951, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10, c_1945])).
% 6.44/2.38  tff(c_2070, plain, (![A_282, B_283, C_284]: (k5_xboole_0(k5_xboole_0(A_282, B_283), C_284)=k5_xboole_0(A_282, k5_xboole_0(B_283, C_284)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.44/2.38  tff(c_2125, plain, (![A_28, C_284]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_284))=k5_xboole_0(k1_xboole_0, C_284))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2070])).
% 6.44/2.38  tff(c_2136, plain, (![A_285, C_286]: (k5_xboole_0(A_285, k5_xboole_0(A_285, C_286))=C_286)), inference(demodulation, [status(thm), theory('equality')], [c_1951, c_2125])).
% 6.44/2.38  tff(c_2188, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=A_28)), inference(superposition, [status(thm), theory('equality')], [c_42, c_2136])).
% 6.44/2.38  tff(c_2249, plain, (![A_288, B_289]: (k5_xboole_0(A_288, k5_xboole_0(B_289, k5_xboole_0(A_288, B_289)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2070, c_42])).
% 6.44/2.38  tff(c_2135, plain, (![A_28, C_284]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_284))=C_284)), inference(demodulation, [status(thm), theory('equality')], [c_1951, c_2125])).
% 6.44/2.38  tff(c_2257, plain, (![B_289, A_288]: (k5_xboole_0(B_289, k5_xboole_0(A_288, B_289))=k5_xboole_0(A_288, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2249, c_2135])).
% 6.44/2.38  tff(c_2331, plain, (![B_289, A_288]: (k5_xboole_0(B_289, k5_xboole_0(A_288, B_289))=A_288)), inference(demodulation, [status(thm), theory('equality')], [c_2188, c_2257])).
% 6.44/2.38  tff(c_1942, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_6')=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1052, c_1912])).
% 6.44/2.38  tff(c_2079, plain, (k5_xboole_0('#skF_6', k5_xboole_0('#skF_7', '#skF_6'))=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2070, c_1942])).
% 6.44/2.38  tff(c_2371, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2331, c_2079])).
% 6.44/2.38  tff(c_32, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.44/2.38  tff(c_2459, plain, (k5_xboole_0('#skF_6', '#skF_7')=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2371, c_32])).
% 6.44/2.38  tff(c_2455, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2371, c_1942])).
% 6.44/2.38  tff(c_2469, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2455, c_2135])).
% 6.44/2.38  tff(c_2817, plain, (k5_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_2469])).
% 6.44/2.38  tff(c_58, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.44/2.38  tff(c_1264, plain, (![B_216, C_217, A_218]: (r2_hidden(B_216, C_217) | ~r1_tarski(k2_tarski(A_218, B_216), C_217))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.44/2.38  tff(c_1341, plain, (![A_230, C_231]: (r2_hidden(A_230, C_231) | ~r1_tarski(k1_tarski(A_230), C_231))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1264])).
% 6.44/2.38  tff(c_1344, plain, (![C_231]: (r2_hidden('#skF_5', C_231) | ~r1_tarski('#skF_6', C_231))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_1341])).
% 6.44/2.38  tff(c_2567, plain, (![A_294, B_295, C_296]: (r2_hidden(A_294, B_295) | r2_hidden(A_294, C_296) | ~r2_hidden(A_294, k5_xboole_0(B_295, C_296)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.44/2.38  tff(c_3266, plain, (![B_307, C_308]: (r2_hidden('#skF_5', B_307) | r2_hidden('#skF_5', C_308) | ~r1_tarski('#skF_6', k5_xboole_0(B_307, C_308)))), inference(resolution, [status(thm)], [c_1344, c_2567])).
% 6.44/2.38  tff(c_3284, plain, (r2_hidden('#skF_5', k4_xboole_0('#skF_6', '#skF_7')) | r2_hidden('#skF_5', '#skF_7') | ~r1_tarski('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2817, c_3266])).
% 6.44/2.38  tff(c_3332, plain, (r2_hidden('#skF_5', k4_xboole_0('#skF_6', '#skF_7')) | r2_hidden('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3284])).
% 6.44/2.38  tff(c_3333, plain, (r2_hidden('#skF_5', k4_xboole_0('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1293, c_3332])).
% 6.44/2.38  tff(c_3179, plain, (![A_304, B_305, C_306]: (r1_tarski(k2_tarski(A_304, B_305), C_306) | ~r2_hidden(B_305, C_306) | ~r2_hidden(A_304, C_306))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.44/2.38  tff(c_7574, plain, (![A_8222, C_8223]: (r1_tarski(k1_tarski(A_8222), C_8223) | ~r2_hidden(A_8222, C_8223) | ~r2_hidden(A_8222, C_8223))), inference(superposition, [status(thm), theory('equality')], [c_58, c_3179])).
% 6.44/2.38  tff(c_7676, plain, (![A_8276, C_8277]: (k2_xboole_0(k1_tarski(A_8276), C_8277)=C_8277 | ~r2_hidden(A_8276, C_8277))), inference(resolution, [status(thm)], [c_7574, c_34])).
% 6.44/2.38  tff(c_38, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.44/2.38  tff(c_7828, plain, (![A_8330, C_8331]: (r1_tarski(k1_tarski(A_8330), C_8331) | ~r2_hidden(A_8330, C_8331))), inference(superposition, [status(thm), theory('equality')], [c_7676, c_38])).
% 6.44/2.38  tff(c_7930, plain, (![C_8384]: (r1_tarski('#skF_6', C_8384) | ~r2_hidden('#skF_5', C_8384))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_7828])).
% 6.44/2.38  tff(c_7995, plain, (r1_tarski('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_3333, c_7930])).
% 6.44/2.38  tff(c_1248, plain, (![B_214, A_215]: (B_214=A_215 | ~r1_tarski(B_214, A_215) | ~r1_tarski(A_215, B_214))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.44/2.38  tff(c_1259, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_36, c_1248])).
% 6.44/2.38  tff(c_8151, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_7995, c_1259])).
% 6.44/2.38  tff(c_44, plain, (![A_29, B_30]: (k5_xboole_0(k5_xboole_0(A_29, B_30), k2_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.44/2.38  tff(c_6546, plain, (![A_7684, B_7685]: (k5_xboole_0(A_7684, k5_xboole_0(B_7685, k2_xboole_0(A_7684, B_7685)))=k3_xboole_0(A_7684, B_7685))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2070])).
% 6.44/2.38  tff(c_6587, plain, (![B_7685, A_7684]: (k5_xboole_0(B_7685, k2_xboole_0(A_7684, B_7685))=k5_xboole_0(A_7684, k3_xboole_0(A_7684, B_7685)))), inference(superposition, [status(thm), theory('equality')], [c_6546, c_2135])).
% 6.44/2.38  tff(c_6830, plain, (![B_7846, A_7847]: (k5_xboole_0(B_7846, k2_xboole_0(A_7847, B_7846))=k4_xboole_0(A_7847, B_7846))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6587])).
% 6.44/2.38  tff(c_7023, plain, (![B_7954, A_7955]: (k5_xboole_0(B_7954, k4_xboole_0(A_7955, B_7954))=k2_xboole_0(A_7955, B_7954))), inference(superposition, [status(thm), theory('equality')], [c_6830, c_2135])).
% 6.44/2.38  tff(c_7064, plain, (![A_7955, B_7954]: (k5_xboole_0(k4_xboole_0(A_7955, B_7954), k2_xboole_0(A_7955, B_7954))=B_7954)), inference(superposition, [status(thm), theory('equality')], [c_7023, c_2331])).
% 6.44/2.38  tff(c_8184, plain, (k5_xboole_0('#skF_6', k2_xboole_0('#skF_6', '#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_8151, c_7064])).
% 6.44/2.38  tff(c_8234, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1052, c_8184])).
% 6.44/2.38  tff(c_8236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1049, c_8234])).
% 6.44/2.38  tff(c_8237, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_1286])).
% 6.44/2.38  tff(c_8243, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_8237, c_34])).
% 6.44/2.38  tff(c_8248, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_8243])).
% 6.44/2.38  tff(c_8250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1107, c_8248])).
% 6.44/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.44/2.38  
% 6.44/2.38  Inference rules
% 6.44/2.38  ----------------------
% 6.44/2.38  #Ref     : 0
% 6.44/2.38  #Sup     : 1754
% 6.44/2.38  #Fact    : 0
% 6.44/2.38  #Define  : 0
% 6.44/2.38  #Split   : 8
% 6.44/2.38  #Chain   : 0
% 6.44/2.38  #Close   : 0
% 6.44/2.38  
% 6.44/2.38  Ordering : KBO
% 6.44/2.38  
% 6.44/2.38  Simplification rules
% 6.44/2.38  ----------------------
% 6.44/2.38  #Subsume      : 156
% 6.44/2.38  #Demod        : 1025
% 6.44/2.38  #Tautology    : 932
% 6.44/2.38  #SimpNegUnit  : 71
% 6.44/2.38  #BackRed      : 22
% 6.44/2.38  
% 6.44/2.38  #Partial instantiations: 3318
% 6.44/2.38  #Strategies tried      : 1
% 6.44/2.38  
% 6.44/2.38  Timing (in seconds)
% 6.44/2.38  ----------------------
% 6.44/2.38  Preprocessing        : 0.37
% 6.44/2.38  Parsing              : 0.19
% 6.44/2.38  CNF conversion       : 0.03
% 6.44/2.38  Main loop            : 1.22
% 6.44/2.38  Inferencing          : 0.46
% 6.44/2.38  Reduction            : 0.44
% 6.44/2.38  Demodulation         : 0.34
% 6.44/2.38  BG Simplification    : 0.05
% 6.44/2.38  Subsumption          : 0.19
% 6.44/2.38  Abstraction          : 0.05
% 6.44/2.38  MUC search           : 0.00
% 6.44/2.38  Cooper               : 0.00
% 6.44/2.38  Total                : 1.63
% 6.44/2.38  Index Insertion      : 0.00
% 6.44/2.38  Index Deletion       : 0.00
% 6.44/2.38  Index Matching       : 0.00
% 6.44/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
