%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:15 EST 2020

% Result     : Theorem 8.21s
% Output     : CNFRefutation 8.47s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 456 expanded)
%              Number of leaves         :   51 ( 161 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 (1023 expanded)
%              Number of equality atoms :  128 ( 899 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_3 > #skF_7 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_128,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_73,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_134,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_79,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_138,plain,
    ( k1_xboole_0 != '#skF_14'
    | k1_tarski('#skF_12') != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_201,plain,(
    k1_tarski('#skF_12') != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_140,plain,
    ( k1_tarski('#skF_12') != '#skF_14'
    | k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_206,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_44,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_5'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_144,plain,(
    k2_xboole_0('#skF_13','#skF_14') = k1_tarski('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_416,plain,(
    ! [D_175,A_176,B_177] :
      ( ~ r2_hidden(D_175,A_176)
      | r2_hidden(D_175,k2_xboole_0(A_176,B_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_426,plain,(
    ! [D_178] :
      ( ~ r2_hidden(D_178,'#skF_13')
      | r2_hidden(D_178,k1_tarski('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_416])).

tff(c_68,plain,(
    ! [C_44,A_40] :
      ( C_44 = A_40
      | ~ r2_hidden(C_44,k1_tarski(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_466,plain,(
    ! [D_181] :
      ( D_181 = '#skF_12'
      | ~ r2_hidden(D_181,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_426,c_68])).

tff(c_470,plain,
    ( '#skF_5'('#skF_13') = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_44,c_466])).

tff(c_473,plain,(
    '#skF_5'('#skF_13') = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_470])).

tff(c_477,plain,
    ( r2_hidden('#skF_12','#skF_13')
    | k1_xboole_0 = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_44])).

tff(c_480,plain,(
    r2_hidden('#skF_12','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_477])).

tff(c_975,plain,(
    ! [B_230,A_231] :
      ( k3_xboole_0(B_230,k1_tarski(A_231)) = k1_tarski(A_231)
      | ~ r2_hidden(A_231,B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    ! [A_27,B_28] : k2_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1057,plain,(
    ! [B_235,A_236] :
      ( k2_xboole_0(B_235,k1_tarski(A_236)) = B_235
      | ~ r2_hidden(A_236,B_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_54])).

tff(c_431,plain,(
    ! [A_179,B_180] : k2_xboole_0(A_179,k2_xboole_0(A_179,B_180)) = k2_xboole_0(A_179,B_180) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_455,plain,(
    k2_xboole_0('#skF_13',k1_tarski('#skF_12')) = k2_xboole_0('#skF_13','#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_431])).

tff(c_464,plain,(
    k2_xboole_0('#skF_13',k1_tarski('#skF_12')) = k1_tarski('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_455])).

tff(c_1066,plain,
    ( k1_tarski('#skF_12') = '#skF_13'
    | ~ r2_hidden('#skF_12','#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_1057,c_464])).

tff(c_1092,plain,(
    k1_tarski('#skF_12') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_1066])).

tff(c_1094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_1092])).

tff(c_1095,plain,(
    k1_tarski('#skF_12') != '#skF_14' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_1157,plain,(
    ! [B_245,A_246] : k5_xboole_0(B_245,A_246) = k5_xboole_0(A_246,B_245) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1096,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_58,plain,(
    ! [A_31] : k5_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1097,plain,(
    ! [A_31] : k5_xboole_0(A_31,'#skF_13') = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_58])).

tff(c_1173,plain,(
    ! [A_246] : k5_xboole_0('#skF_13',A_246) = A_246 ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_1097])).

tff(c_1131,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_5'(A_19),A_19)
      | A_19 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_44])).

tff(c_128,plain,(
    ! [B_139] : r1_tarski(k1_tarski(B_139),k1_tarski(B_139)) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1278,plain,(
    ! [A_255,B_256] :
      ( k4_xboole_0(A_255,B_256) = '#skF_13'
      | ~ r1_tarski(A_255,B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_48])).

tff(c_1290,plain,(
    ! [B_139] : k4_xboole_0(k1_tarski(B_139),k1_tarski(B_139)) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_128,c_1278])).

tff(c_134,plain,(
    ! [B_143] : k4_xboole_0(k1_tarski(B_143),k1_tarski(B_143)) != k1_tarski(B_143) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1298,plain,(
    ! [B_143] : k1_tarski(B_143) != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_134])).

tff(c_1738,plain,(
    ! [B_298,A_299] :
      ( k3_xboole_0(B_298,k1_tarski(A_299)) = k1_tarski(A_299)
      | ~ r2_hidden(A_299,B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1386,plain,(
    ! [A_270,B_271] : k5_xboole_0(A_270,k3_xboole_0(A_270,B_271)) = k4_xboole_0(A_270,B_271) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1442,plain,(
    ! [B_274] : k4_xboole_0('#skF_13',B_274) = k3_xboole_0('#skF_13',B_274) ),
    inference(superposition,[status(thm),theory(equality)],[c_1386,c_1173])).

tff(c_130,plain,(
    ! [B_139] : r1_tarski(k1_xboole_0,k1_tarski(B_139)) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1099,plain,(
    ! [B_139] : r1_tarski('#skF_13',k1_tarski(B_139)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_130])).

tff(c_1289,plain,(
    ! [B_139] : k4_xboole_0('#skF_13',k1_tarski(B_139)) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_1099,c_1278])).

tff(c_1455,plain,(
    ! [B_139] : k3_xboole_0('#skF_13',k1_tarski(B_139)) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_1289])).

tff(c_1752,plain,(
    ! [A_299] :
      ( k1_tarski(A_299) = '#skF_13'
      | ~ r2_hidden(A_299,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1738,c_1455])).

tff(c_1778,plain,(
    ! [A_299] : ~ r2_hidden(A_299,'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_1298,c_1752])).

tff(c_2329,plain,(
    ! [A_321,B_322] : k5_xboole_0(k5_xboole_0(A_321,B_322),k2_xboole_0(A_321,B_322)) = k3_xboole_0(A_321,B_322) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4667,plain,(
    ! [A_6353] : k5_xboole_0(A_6353,k2_xboole_0('#skF_13',A_6353)) = k3_xboole_0('#skF_13',A_6353) ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_2329])).

tff(c_4736,plain,(
    ! [B_28] : k5_xboole_0(k3_xboole_0('#skF_13',B_28),'#skF_13') = k3_xboole_0('#skF_13',k3_xboole_0('#skF_13',B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4667])).

tff(c_5115,plain,(
    ! [B_6680] : k3_xboole_0('#skF_13',k3_xboole_0('#skF_13',B_6680)) = k3_xboole_0('#skF_13',B_6680) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_4736])).

tff(c_26,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,A_9)
      | ~ r2_hidden(D_14,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5136,plain,(
    ! [D_14,B_6680] :
      ( r2_hidden(D_14,'#skF_13')
      | ~ r2_hidden(D_14,k3_xboole_0('#skF_13',B_6680)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5115,c_26])).

tff(c_5255,plain,(
    ! [D_7004,B_7005] : ~ r2_hidden(D_7004,k3_xboole_0('#skF_13',B_7005)) ),
    inference(negUnitSimplification,[status(thm)],[c_1778,c_5136])).

tff(c_5285,plain,(
    ! [B_7005] : k3_xboole_0('#skF_13',B_7005) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_1131,c_5255])).

tff(c_2432,plain,(
    k5_xboole_0(k5_xboole_0('#skF_13','#skF_14'),k1_tarski('#skF_12')) = k3_xboole_0('#skF_13','#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_2329])).

tff(c_2447,plain,(
    k5_xboole_0('#skF_14',k1_tarski('#skF_12')) = k3_xboole_0('#skF_13','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_2432])).

tff(c_64,plain,(
    ! [A_37] : k5_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1098,plain,(
    ! [A_37] : k5_xboole_0(A_37,A_37) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_64])).

tff(c_1847,plain,(
    ! [A_306,B_307,C_308] : k5_xboole_0(k5_xboole_0(A_306,B_307),C_308) = k5_xboole_0(A_306,k5_xboole_0(B_307,C_308)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1911,plain,(
    ! [A_37,C_308] : k5_xboole_0(A_37,k5_xboole_0(A_37,C_308)) = k5_xboole_0('#skF_13',C_308) ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_1847])).

tff(c_1924,plain,(
    ! [A_37,C_308] : k5_xboole_0(A_37,k5_xboole_0(A_37,C_308)) = C_308 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_1911])).

tff(c_2535,plain,(
    k5_xboole_0('#skF_14',k3_xboole_0('#skF_13','#skF_14')) = k1_tarski('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2447,c_1924])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1925,plain,(
    ! [A_309,C_310] : k5_xboole_0(A_309,k5_xboole_0(A_309,C_310)) = C_310 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_1911])).

tff(c_1968,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1925])).

tff(c_2677,plain,(
    k5_xboole_0(k3_xboole_0('#skF_13','#skF_14'),k1_tarski('#skF_12')) = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_2535,c_1968])).

tff(c_2749,plain,(
    k5_xboole_0(k3_xboole_0('#skF_13','#skF_14'),'#skF_14') = k1_tarski('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2677,c_1924])).

tff(c_5318,plain,(
    k5_xboole_0('#skF_13','#skF_14') = k1_tarski('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5285,c_2749])).

tff(c_5326,plain,(
    k1_tarski('#skF_12') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_5318])).

tff(c_5328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1095,c_5326])).

tff(c_5330,plain,(
    k1_tarski('#skF_12') = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_142,plain,
    ( k1_tarski('#skF_12') != '#skF_14'
    | k1_tarski('#skF_12') != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5357,plain,(
    '#skF_14' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5330,c_5330,c_142])).

tff(c_8795,plain,(
    ! [A_7273] :
      ( '#skF_6'(A_7273,'#skF_14') = A_7273
      | '#skF_7'(A_7273,'#skF_14') != A_7273
      | k1_tarski(A_7273) = '#skF_14' ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8798,plain,
    ( '#skF_14' = '#skF_13'
    | '#skF_6'('#skF_12','#skF_14') = '#skF_12'
    | '#skF_7'('#skF_12','#skF_14') != '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_8795,c_5330])).

tff(c_9237,plain,
    ( '#skF_6'('#skF_12','#skF_14') = '#skF_12'
    | '#skF_7'('#skF_12','#skF_14') != '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_5357,c_8798])).

tff(c_9328,plain,(
    '#skF_7'('#skF_12','#skF_14') != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_9237])).

tff(c_5329,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_5349,plain,(
    k2_xboole_0('#skF_13','#skF_14') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5330,c_144])).

tff(c_5660,plain,(
    ! [D_7198,B_7199,A_7200] :
      ( ~ r2_hidden(D_7198,B_7199)
      | r2_hidden(D_7198,k2_xboole_0(A_7200,B_7199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5670,plain,(
    ! [D_7201] :
      ( ~ r2_hidden(D_7201,'#skF_14')
      | r2_hidden(D_7201,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5349,c_5660])).

tff(c_5674,plain,
    ( r2_hidden('#skF_5'('#skF_14'),'#skF_13')
    | k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_44,c_5670])).

tff(c_5677,plain,(
    r2_hidden('#skF_5'('#skF_14'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_5329,c_5674])).

tff(c_5468,plain,(
    ! [C_7172,A_7173] :
      ( C_7172 = A_7173
      | ~ r2_hidden(C_7172,k1_tarski(A_7173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5471,plain,(
    ! [C_7172] :
      ( C_7172 = '#skF_12'
      | ~ r2_hidden(C_7172,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5330,c_5468])).

tff(c_5681,plain,(
    '#skF_5'('#skF_14') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5677,c_5471])).

tff(c_5687,plain,
    ( r2_hidden('#skF_12','#skF_14')
    | k1_xboole_0 = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_5681,c_44])).

tff(c_5690,plain,(
    r2_hidden('#skF_12','#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_5329,c_5687])).

tff(c_10438,plain,(
    ! [A_16500,B_16501] :
      ( '#skF_6'(A_16500,B_16501) = A_16500
      | r2_hidden('#skF_7'(A_16500,B_16501),B_16501)
      | k1_tarski(A_16500) = B_16501 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5666,plain,(
    ! [D_7198] :
      ( ~ r2_hidden(D_7198,'#skF_14')
      | r2_hidden(D_7198,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5349,c_5660])).

tff(c_12155,plain,(
    ! [A_19580] :
      ( r2_hidden('#skF_7'(A_19580,'#skF_14'),'#skF_13')
      | '#skF_6'(A_19580,'#skF_14') = A_19580
      | k1_tarski(A_19580) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_10438,c_5666])).

tff(c_12445,plain,(
    ! [A_19992] :
      ( '#skF_7'(A_19992,'#skF_14') = '#skF_12'
      | '#skF_6'(A_19992,'#skF_14') = A_19992
      | k1_tarski(A_19992) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_12155,c_5471])).

tff(c_12495,plain,
    ( '#skF_14' = '#skF_13'
    | '#skF_7'('#skF_12','#skF_14') = '#skF_12'
    | '#skF_6'('#skF_12','#skF_14') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_12445,c_5330])).

tff(c_12592,plain,(
    '#skF_6'('#skF_12','#skF_14') = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_9328,c_5357,c_12495])).

tff(c_76,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_6'(A_40,B_41),B_41)
      | r2_hidden('#skF_7'(A_40,B_41),B_41)
      | k1_tarski(A_40) = B_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12605,plain,
    ( ~ r2_hidden('#skF_12','#skF_14')
    | r2_hidden('#skF_7'('#skF_12','#skF_14'),'#skF_14')
    | k1_tarski('#skF_12') = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_12592,c_76])).

tff(c_12632,plain,
    ( r2_hidden('#skF_7'('#skF_12','#skF_14'),'#skF_14')
    | '#skF_14' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5330,c_5690,c_12605])).

tff(c_12633,plain,(
    r2_hidden('#skF_7'('#skF_12','#skF_14'),'#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_5357,c_12632])).

tff(c_12647,plain,(
    r2_hidden('#skF_7'('#skF_12','#skF_14'),'#skF_13') ),
    inference(resolution,[status(thm)],[c_12633,c_5666])).

tff(c_12652,plain,(
    '#skF_7'('#skF_12','#skF_14') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_12647,c_5471])).

tff(c_12659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9328,c_12652])).

tff(c_12661,plain,(
    '#skF_7'('#skF_12','#skF_14') = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_9237])).

tff(c_12660,plain,(
    '#skF_6'('#skF_12','#skF_14') = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_9237])).

tff(c_13512,plain,(
    ! [A_22094,B_22095] :
      ( ~ r2_hidden('#skF_6'(A_22094,B_22095),B_22095)
      | '#skF_7'(A_22094,B_22095) != A_22094
      | k1_tarski(A_22094) = B_22095 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13521,plain,
    ( ~ r2_hidden('#skF_12','#skF_14')
    | '#skF_7'('#skF_12','#skF_14') != '#skF_12'
    | k1_tarski('#skF_12') = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_12660,c_13512])).

tff(c_13577,plain,(
    '#skF_14' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5330,c_12661,c_5690,c_13521])).

tff(c_13579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5357,c_13577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:29:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.21/2.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.21/2.69  
% 8.21/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.21/2.69  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_3 > #skF_7 > #skF_9 > #skF_12
% 8.21/2.69  
% 8.21/2.69  %Foreground sorts:
% 8.21/2.69  
% 8.21/2.69  
% 8.21/2.69  %Background operators:
% 8.21/2.69  
% 8.21/2.69  
% 8.21/2.69  %Foreground operators:
% 8.21/2.69  tff('#skF_5', type, '#skF_5': $i > $i).
% 8.21/2.69  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.21/2.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.21/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.21/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.21/2.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.21/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.21/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.21/2.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.21/2.69  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.21/2.69  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.21/2.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.21/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.21/2.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.21/2.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.21/2.69  tff('#skF_14', type, '#skF_14': $i).
% 8.21/2.69  tff('#skF_13', type, '#skF_13': $i).
% 8.21/2.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.21/2.69  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 8.21/2.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.21/2.69  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.21/2.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.21/2.69  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 8.21/2.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.21/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.21/2.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.21/2.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.21/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.21/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.21/2.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.21/2.69  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.21/2.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.21/2.69  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.21/2.69  tff('#skF_12', type, '#skF_12': $i).
% 8.21/2.69  
% 8.21/2.72  tff(f_160, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 8.21/2.72  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.21/2.72  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 8.21/2.72  tff(f_88, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.21/2.72  tff(f_128, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 8.21/2.72  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.21/2.72  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 8.21/2.72  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.21/2.72  tff(f_73, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.21/2.72  tff(f_134, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 8.21/2.72  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.21/2.72  tff(f_141, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 8.21/2.72  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.21/2.72  tff(f_81, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.21/2.72  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.21/2.72  tff(f_79, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.21/2.72  tff(f_77, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.21/2.72  tff(c_138, plain, (k1_xboole_0!='#skF_14' | k1_tarski('#skF_12')!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.21/2.72  tff(c_201, plain, (k1_tarski('#skF_12')!='#skF_13'), inference(splitLeft, [status(thm)], [c_138])).
% 8.21/2.72  tff(c_140, plain, (k1_tarski('#skF_12')!='#skF_14' | k1_xboole_0!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.21/2.72  tff(c_206, plain, (k1_xboole_0!='#skF_13'), inference(splitLeft, [status(thm)], [c_140])).
% 8.21/2.72  tff(c_44, plain, (![A_19]: (r2_hidden('#skF_5'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.21/2.72  tff(c_144, plain, (k2_xboole_0('#skF_13', '#skF_14')=k1_tarski('#skF_12')), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.21/2.72  tff(c_416, plain, (![D_175, A_176, B_177]: (~r2_hidden(D_175, A_176) | r2_hidden(D_175, k2_xboole_0(A_176, B_177)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.21/2.72  tff(c_426, plain, (![D_178]: (~r2_hidden(D_178, '#skF_13') | r2_hidden(D_178, k1_tarski('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_144, c_416])).
% 8.21/2.72  tff(c_68, plain, (![C_44, A_40]: (C_44=A_40 | ~r2_hidden(C_44, k1_tarski(A_40)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.21/2.72  tff(c_466, plain, (![D_181]: (D_181='#skF_12' | ~r2_hidden(D_181, '#skF_13'))), inference(resolution, [status(thm)], [c_426, c_68])).
% 8.21/2.72  tff(c_470, plain, ('#skF_5'('#skF_13')='#skF_12' | k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_44, c_466])).
% 8.21/2.72  tff(c_473, plain, ('#skF_5'('#skF_13')='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_206, c_470])).
% 8.21/2.72  tff(c_477, plain, (r2_hidden('#skF_12', '#skF_13') | k1_xboole_0='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_473, c_44])).
% 8.21/2.72  tff(c_480, plain, (r2_hidden('#skF_12', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_206, c_477])).
% 8.21/2.72  tff(c_975, plain, (![B_230, A_231]: (k3_xboole_0(B_230, k1_tarski(A_231))=k1_tarski(A_231) | ~r2_hidden(A_231, B_230))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.21/2.72  tff(c_54, plain, (![A_27, B_28]: (k2_xboole_0(A_27, k3_xboole_0(A_27, B_28))=A_27)), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.21/2.72  tff(c_1057, plain, (![B_235, A_236]: (k2_xboole_0(B_235, k1_tarski(A_236))=B_235 | ~r2_hidden(A_236, B_235))), inference(superposition, [status(thm), theory('equality')], [c_975, c_54])).
% 8.21/2.72  tff(c_431, plain, (![A_179, B_180]: (k2_xboole_0(A_179, k2_xboole_0(A_179, B_180))=k2_xboole_0(A_179, B_180))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.21/2.72  tff(c_455, plain, (k2_xboole_0('#skF_13', k1_tarski('#skF_12'))=k2_xboole_0('#skF_13', '#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_144, c_431])).
% 8.21/2.72  tff(c_464, plain, (k2_xboole_0('#skF_13', k1_tarski('#skF_12'))=k1_tarski('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_455])).
% 8.21/2.72  tff(c_1066, plain, (k1_tarski('#skF_12')='#skF_13' | ~r2_hidden('#skF_12', '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_1057, c_464])).
% 8.21/2.72  tff(c_1092, plain, (k1_tarski('#skF_12')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_1066])).
% 8.21/2.72  tff(c_1094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_1092])).
% 8.21/2.72  tff(c_1095, plain, (k1_tarski('#skF_12')!='#skF_14'), inference(splitRight, [status(thm)], [c_140])).
% 8.21/2.72  tff(c_1157, plain, (![B_245, A_246]: (k5_xboole_0(B_245, A_246)=k5_xboole_0(A_246, B_245))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.21/2.72  tff(c_1096, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_140])).
% 8.21/2.72  tff(c_58, plain, (![A_31]: (k5_xboole_0(A_31, k1_xboole_0)=A_31)), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.21/2.72  tff(c_1097, plain, (![A_31]: (k5_xboole_0(A_31, '#skF_13')=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_58])).
% 8.21/2.72  tff(c_1173, plain, (![A_246]: (k5_xboole_0('#skF_13', A_246)=A_246)), inference(superposition, [status(thm), theory('equality')], [c_1157, c_1097])).
% 8.21/2.72  tff(c_1131, plain, (![A_19]: (r2_hidden('#skF_5'(A_19), A_19) | A_19='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_44])).
% 8.21/2.72  tff(c_128, plain, (![B_139]: (r1_tarski(k1_tarski(B_139), k1_tarski(B_139)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.21/2.72  tff(c_48, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.21/2.72  tff(c_1278, plain, (![A_255, B_256]: (k4_xboole_0(A_255, B_256)='#skF_13' | ~r1_tarski(A_255, B_256))), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_48])).
% 8.21/2.72  tff(c_1290, plain, (![B_139]: (k4_xboole_0(k1_tarski(B_139), k1_tarski(B_139))='#skF_13')), inference(resolution, [status(thm)], [c_128, c_1278])).
% 8.21/2.72  tff(c_134, plain, (![B_143]: (k4_xboole_0(k1_tarski(B_143), k1_tarski(B_143))!=k1_tarski(B_143))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.21/2.72  tff(c_1298, plain, (![B_143]: (k1_tarski(B_143)!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_134])).
% 8.21/2.72  tff(c_1738, plain, (![B_298, A_299]: (k3_xboole_0(B_298, k1_tarski(A_299))=k1_tarski(A_299) | ~r2_hidden(A_299, B_298))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.21/2.72  tff(c_1386, plain, (![A_270, B_271]: (k5_xboole_0(A_270, k3_xboole_0(A_270, B_271))=k4_xboole_0(A_270, B_271))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.21/2.72  tff(c_1442, plain, (![B_274]: (k4_xboole_0('#skF_13', B_274)=k3_xboole_0('#skF_13', B_274))), inference(superposition, [status(thm), theory('equality')], [c_1386, c_1173])).
% 8.21/2.72  tff(c_130, plain, (![B_139]: (r1_tarski(k1_xboole_0, k1_tarski(B_139)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.21/2.72  tff(c_1099, plain, (![B_139]: (r1_tarski('#skF_13', k1_tarski(B_139)))), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_130])).
% 8.21/2.72  tff(c_1289, plain, (![B_139]: (k4_xboole_0('#skF_13', k1_tarski(B_139))='#skF_13')), inference(resolution, [status(thm)], [c_1099, c_1278])).
% 8.21/2.72  tff(c_1455, plain, (![B_139]: (k3_xboole_0('#skF_13', k1_tarski(B_139))='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_1442, c_1289])).
% 8.21/2.72  tff(c_1752, plain, (![A_299]: (k1_tarski(A_299)='#skF_13' | ~r2_hidden(A_299, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_1738, c_1455])).
% 8.21/2.72  tff(c_1778, plain, (![A_299]: (~r2_hidden(A_299, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_1298, c_1752])).
% 8.21/2.72  tff(c_2329, plain, (![A_321, B_322]: (k5_xboole_0(k5_xboole_0(A_321, B_322), k2_xboole_0(A_321, B_322))=k3_xboole_0(A_321, B_322))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.21/2.72  tff(c_4667, plain, (![A_6353]: (k5_xboole_0(A_6353, k2_xboole_0('#skF_13', A_6353))=k3_xboole_0('#skF_13', A_6353))), inference(superposition, [status(thm), theory('equality')], [c_1173, c_2329])).
% 8.21/2.72  tff(c_4736, plain, (![B_28]: (k5_xboole_0(k3_xboole_0('#skF_13', B_28), '#skF_13')=k3_xboole_0('#skF_13', k3_xboole_0('#skF_13', B_28)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4667])).
% 8.21/2.72  tff(c_5115, plain, (![B_6680]: (k3_xboole_0('#skF_13', k3_xboole_0('#skF_13', B_6680))=k3_xboole_0('#skF_13', B_6680))), inference(demodulation, [status(thm), theory('equality')], [c_1097, c_4736])).
% 8.21/2.72  tff(c_26, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, A_9) | ~r2_hidden(D_14, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.21/2.72  tff(c_5136, plain, (![D_14, B_6680]: (r2_hidden(D_14, '#skF_13') | ~r2_hidden(D_14, k3_xboole_0('#skF_13', B_6680)))), inference(superposition, [status(thm), theory('equality')], [c_5115, c_26])).
% 8.21/2.72  tff(c_5255, plain, (![D_7004, B_7005]: (~r2_hidden(D_7004, k3_xboole_0('#skF_13', B_7005)))), inference(negUnitSimplification, [status(thm)], [c_1778, c_5136])).
% 8.21/2.72  tff(c_5285, plain, (![B_7005]: (k3_xboole_0('#skF_13', B_7005)='#skF_13')), inference(resolution, [status(thm)], [c_1131, c_5255])).
% 8.21/2.72  tff(c_2432, plain, (k5_xboole_0(k5_xboole_0('#skF_13', '#skF_14'), k1_tarski('#skF_12'))=k3_xboole_0('#skF_13', '#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_144, c_2329])).
% 8.21/2.72  tff(c_2447, plain, (k5_xboole_0('#skF_14', k1_tarski('#skF_12'))=k3_xboole_0('#skF_13', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_2432])).
% 8.21/2.72  tff(c_64, plain, (![A_37]: (k5_xboole_0(A_37, A_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.21/2.72  tff(c_1098, plain, (![A_37]: (k5_xboole_0(A_37, A_37)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_64])).
% 8.21/2.72  tff(c_1847, plain, (![A_306, B_307, C_308]: (k5_xboole_0(k5_xboole_0(A_306, B_307), C_308)=k5_xboole_0(A_306, k5_xboole_0(B_307, C_308)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.21/2.72  tff(c_1911, plain, (![A_37, C_308]: (k5_xboole_0(A_37, k5_xboole_0(A_37, C_308))=k5_xboole_0('#skF_13', C_308))), inference(superposition, [status(thm), theory('equality')], [c_1098, c_1847])).
% 8.21/2.72  tff(c_1924, plain, (![A_37, C_308]: (k5_xboole_0(A_37, k5_xboole_0(A_37, C_308))=C_308)), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_1911])).
% 8.21/2.72  tff(c_2535, plain, (k5_xboole_0('#skF_14', k3_xboole_0('#skF_13', '#skF_14'))=k1_tarski('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_2447, c_1924])).
% 8.21/2.72  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.21/2.72  tff(c_1925, plain, (![A_309, C_310]: (k5_xboole_0(A_309, k5_xboole_0(A_309, C_310))=C_310)), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_1911])).
% 8.21/2.72  tff(c_1968, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1925])).
% 8.21/2.72  tff(c_2677, plain, (k5_xboole_0(k3_xboole_0('#skF_13', '#skF_14'), k1_tarski('#skF_12'))='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_2535, c_1968])).
% 8.21/2.72  tff(c_2749, plain, (k5_xboole_0(k3_xboole_0('#skF_13', '#skF_14'), '#skF_14')=k1_tarski('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_2677, c_1924])).
% 8.21/2.72  tff(c_5318, plain, (k5_xboole_0('#skF_13', '#skF_14')=k1_tarski('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5285, c_2749])).
% 8.21/2.72  tff(c_5326, plain, (k1_tarski('#skF_12')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_5318])).
% 8.21/2.72  tff(c_5328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1095, c_5326])).
% 8.21/2.72  tff(c_5330, plain, (k1_tarski('#skF_12')='#skF_13'), inference(splitRight, [status(thm)], [c_138])).
% 8.21/2.72  tff(c_142, plain, (k1_tarski('#skF_12')!='#skF_14' | k1_tarski('#skF_12')!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.21/2.72  tff(c_5357, plain, ('#skF_14'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5330, c_5330, c_142])).
% 8.21/2.72  tff(c_8795, plain, (![A_7273]: ('#skF_6'(A_7273, '#skF_14')=A_7273 | '#skF_7'(A_7273, '#skF_14')!=A_7273 | k1_tarski(A_7273)='#skF_14')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.21/2.72  tff(c_8798, plain, ('#skF_14'='#skF_13' | '#skF_6'('#skF_12', '#skF_14')='#skF_12' | '#skF_7'('#skF_12', '#skF_14')!='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_8795, c_5330])).
% 8.21/2.72  tff(c_9237, plain, ('#skF_6'('#skF_12', '#skF_14')='#skF_12' | '#skF_7'('#skF_12', '#skF_14')!='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_5357, c_8798])).
% 8.47/2.72  tff(c_9328, plain, ('#skF_7'('#skF_12', '#skF_14')!='#skF_12'), inference(splitLeft, [status(thm)], [c_9237])).
% 8.47/2.72  tff(c_5329, plain, (k1_xboole_0!='#skF_14'), inference(splitRight, [status(thm)], [c_138])).
% 8.47/2.72  tff(c_5349, plain, (k2_xboole_0('#skF_13', '#skF_14')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5330, c_144])).
% 8.47/2.72  tff(c_5660, plain, (![D_7198, B_7199, A_7200]: (~r2_hidden(D_7198, B_7199) | r2_hidden(D_7198, k2_xboole_0(A_7200, B_7199)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.47/2.72  tff(c_5670, plain, (![D_7201]: (~r2_hidden(D_7201, '#skF_14') | r2_hidden(D_7201, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_5349, c_5660])).
% 8.47/2.72  tff(c_5674, plain, (r2_hidden('#skF_5'('#skF_14'), '#skF_13') | k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_44, c_5670])).
% 8.47/2.72  tff(c_5677, plain, (r2_hidden('#skF_5'('#skF_14'), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_5329, c_5674])).
% 8.47/2.72  tff(c_5468, plain, (![C_7172, A_7173]: (C_7172=A_7173 | ~r2_hidden(C_7172, k1_tarski(A_7173)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.47/2.72  tff(c_5471, plain, (![C_7172]: (C_7172='#skF_12' | ~r2_hidden(C_7172, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_5330, c_5468])).
% 8.47/2.72  tff(c_5681, plain, ('#skF_5'('#skF_14')='#skF_12'), inference(resolution, [status(thm)], [c_5677, c_5471])).
% 8.47/2.72  tff(c_5687, plain, (r2_hidden('#skF_12', '#skF_14') | k1_xboole_0='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_5681, c_44])).
% 8.47/2.72  tff(c_5690, plain, (r2_hidden('#skF_12', '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_5329, c_5687])).
% 8.47/2.72  tff(c_10438, plain, (![A_16500, B_16501]: ('#skF_6'(A_16500, B_16501)=A_16500 | r2_hidden('#skF_7'(A_16500, B_16501), B_16501) | k1_tarski(A_16500)=B_16501)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.47/2.72  tff(c_5666, plain, (![D_7198]: (~r2_hidden(D_7198, '#skF_14') | r2_hidden(D_7198, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_5349, c_5660])).
% 8.47/2.72  tff(c_12155, plain, (![A_19580]: (r2_hidden('#skF_7'(A_19580, '#skF_14'), '#skF_13') | '#skF_6'(A_19580, '#skF_14')=A_19580 | k1_tarski(A_19580)='#skF_14')), inference(resolution, [status(thm)], [c_10438, c_5666])).
% 8.47/2.72  tff(c_12445, plain, (![A_19992]: ('#skF_7'(A_19992, '#skF_14')='#skF_12' | '#skF_6'(A_19992, '#skF_14')=A_19992 | k1_tarski(A_19992)='#skF_14')), inference(resolution, [status(thm)], [c_12155, c_5471])).
% 8.47/2.72  tff(c_12495, plain, ('#skF_14'='#skF_13' | '#skF_7'('#skF_12', '#skF_14')='#skF_12' | '#skF_6'('#skF_12', '#skF_14')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_12445, c_5330])).
% 8.47/2.72  tff(c_12592, plain, ('#skF_6'('#skF_12', '#skF_14')='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_9328, c_5357, c_12495])).
% 8.47/2.72  tff(c_76, plain, (![A_40, B_41]: (~r2_hidden('#skF_6'(A_40, B_41), B_41) | r2_hidden('#skF_7'(A_40, B_41), B_41) | k1_tarski(A_40)=B_41)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.47/2.72  tff(c_12605, plain, (~r2_hidden('#skF_12', '#skF_14') | r2_hidden('#skF_7'('#skF_12', '#skF_14'), '#skF_14') | k1_tarski('#skF_12')='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_12592, c_76])).
% 8.47/2.72  tff(c_12632, plain, (r2_hidden('#skF_7'('#skF_12', '#skF_14'), '#skF_14') | '#skF_14'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5330, c_5690, c_12605])).
% 8.47/2.72  tff(c_12633, plain, (r2_hidden('#skF_7'('#skF_12', '#skF_14'), '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_5357, c_12632])).
% 8.47/2.72  tff(c_12647, plain, (r2_hidden('#skF_7'('#skF_12', '#skF_14'), '#skF_13')), inference(resolution, [status(thm)], [c_12633, c_5666])).
% 8.47/2.72  tff(c_12652, plain, ('#skF_7'('#skF_12', '#skF_14')='#skF_12'), inference(resolution, [status(thm)], [c_12647, c_5471])).
% 8.47/2.72  tff(c_12659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9328, c_12652])).
% 8.47/2.72  tff(c_12661, plain, ('#skF_7'('#skF_12', '#skF_14')='#skF_12'), inference(splitRight, [status(thm)], [c_9237])).
% 8.47/2.72  tff(c_12660, plain, ('#skF_6'('#skF_12', '#skF_14')='#skF_12'), inference(splitRight, [status(thm)], [c_9237])).
% 8.47/2.72  tff(c_13512, plain, (![A_22094, B_22095]: (~r2_hidden('#skF_6'(A_22094, B_22095), B_22095) | '#skF_7'(A_22094, B_22095)!=A_22094 | k1_tarski(A_22094)=B_22095)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.47/2.72  tff(c_13521, plain, (~r2_hidden('#skF_12', '#skF_14') | '#skF_7'('#skF_12', '#skF_14')!='#skF_12' | k1_tarski('#skF_12')='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_12660, c_13512])).
% 8.47/2.72  tff(c_13577, plain, ('#skF_14'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5330, c_12661, c_5690, c_13521])).
% 8.47/2.72  tff(c_13579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5357, c_13577])).
% 8.47/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.47/2.72  
% 8.47/2.72  Inference rules
% 8.47/2.72  ----------------------
% 8.47/2.72  #Ref     : 0
% 8.47/2.72  #Sup     : 2399
% 8.47/2.72  #Fact    : 0
% 8.47/2.72  #Define  : 0
% 8.47/2.72  #Split   : 11
% 8.47/2.72  #Chain   : 0
% 8.47/2.72  #Close   : 0
% 8.47/2.72  
% 8.47/2.72  Ordering : KBO
% 8.47/2.72  
% 8.47/2.72  Simplification rules
% 8.47/2.72  ----------------------
% 8.47/2.72  #Subsume      : 243
% 8.47/2.72  #Demod        : 1539
% 8.47/2.72  #Tautology    : 1464
% 8.47/2.72  #SimpNegUnit  : 190
% 8.47/2.72  #BackRed      : 113
% 8.47/2.72  
% 8.47/2.72  #Partial instantiations: 7801
% 8.47/2.72  #Strategies tried      : 1
% 8.47/2.72  
% 8.47/2.72  Timing (in seconds)
% 8.47/2.72  ----------------------
% 8.47/2.72  Preprocessing        : 0.42
% 8.47/2.72  Parsing              : 0.21
% 8.47/2.72  CNF conversion       : 0.04
% 8.47/2.72  Main loop            : 1.51
% 8.47/2.72  Inferencing          : 0.64
% 8.47/2.72  Reduction            : 0.50
% 8.47/2.72  Demodulation         : 0.38
% 8.47/2.72  BG Simplification    : 0.06
% 8.47/2.72  Subsumption          : 0.21
% 8.47/2.72  Abstraction          : 0.06
% 8.47/2.72  MUC search           : 0.00
% 8.47/2.72  Cooper               : 0.00
% 8.47/2.72  Total                : 1.98
% 8.47/2.72  Index Insertion      : 0.00
% 8.47/2.72  Index Deletion       : 0.00
% 8.47/2.72  Index Matching       : 0.00
% 8.47/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
