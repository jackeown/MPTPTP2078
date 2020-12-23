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
% DateTime   : Thu Dec  3 09:49:56 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 269 expanded)
%              Number of leaves         :   33 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 471 expanded)
%              Number of equality atoms :   43 ( 179 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_63,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_18,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_40,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tarski(A_46),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_188,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_54,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_323,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | ~ r1_tarski(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_325,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_323,c_14])).

tff(c_331,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_325])).

tff(c_336,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_331])).

tff(c_42,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(k1_tarski(A_48),B_49)
      | r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_332,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_323,c_20])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_279,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_344,plain,(
    ! [A_87,B_88] :
      ( ~ r1_xboole_0(A_87,B_88)
      | v1_xboole_0(k3_xboole_0(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_6,c_279])).

tff(c_350,plain,
    ( ~ r1_xboole_0('#skF_5',k1_tarski('#skF_6'))
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_344])).

tff(c_428,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_369,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_2'(A_89,B_90),k3_xboole_0(A_89,B_90))
      | r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_429,plain,(
    ! [A_94,B_95] :
      ( ~ v1_xboole_0(k3_xboole_0(A_94,B_95))
      | r1_xboole_0(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_369,c_4])).

tff(c_435,plain,
    ( ~ v1_xboole_0('#skF_5')
    | r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_429])).

tff(c_452,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_435])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_494,plain,(
    ! [A_103,B_104] :
      ( ~ r1_xboole_0(A_103,B_104)
      | v1_xboole_0(k3_xboole_0(B_104,A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_344])).

tff(c_503,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_494])).

tff(c_521,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_503])).

tff(c_528,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_521])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_528])).

tff(c_533,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_537,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_533,c_8])).

tff(c_541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_537])).

tff(c_542,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_544,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_542])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_235,plain,(
    ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_545,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_235])).

tff(c_548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_545])).

tff(c_549,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_22,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_558,plain,(
    ! [A_17] : r1_tarski('#skF_3',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_22])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_235])).

tff(c_566,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_618,plain,(
    ! [B_109,A_110] :
      ( B_109 = A_110
      | ~ r1_tarski(B_109,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_622,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_566,c_618])).

tff(c_632,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_622])).

tff(c_647,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_632])).

tff(c_571,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_566,c_20])).

tff(c_584,plain,(
    ! [A_105,B_106,C_107] :
      ( ~ r1_xboole_0(A_105,B_106)
      | ~ r2_hidden(C_107,k3_xboole_0(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_673,plain,(
    ! [A_114,B_115] :
      ( ~ r1_xboole_0(A_114,B_115)
      | v1_xboole_0(k3_xboole_0(A_114,B_115)) ) ),
    inference(resolution,[status(thm)],[c_6,c_584])).

tff(c_682,plain,
    ( ~ r1_xboole_0('#skF_5',k1_tarski('#skF_6'))
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_673])).

tff(c_719,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_682])).

tff(c_939,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_2'(A_132,B_133),k3_xboole_0(A_132,B_133))
      | r1_xboole_0(A_132,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_948,plain,
    ( r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_939])).

tff(c_966,plain,(
    r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_719,c_948])).

tff(c_995,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_966,c_4])).

tff(c_1192,plain,(
    ! [B_153,A_154] :
      ( ~ r1_xboole_0(B_153,A_154)
      | v1_xboole_0(k3_xboole_0(A_154,B_153)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_673])).

tff(c_1204,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_1192])).

tff(c_1223,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_995,c_1204])).

tff(c_1239,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1223])).

tff(c_1243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_647,c_1239])).

tff(c_1244,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_682])).

tff(c_1248,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1244,c_8])).

tff(c_1252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_1248])).

tff(c_1254,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1356,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_46])).

tff(c_1357,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1356])).

tff(c_1363,plain,(
    ! [A_17] : r1_tarski('#skF_3',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_22])).

tff(c_1253,plain,(
    ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1363,c_1253])).

tff(c_1371,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1356])).

tff(c_1373,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_1253])).

tff(c_1376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1373])).

tff(c_1378,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1388,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1378,c_1378,c_50])).

tff(c_1389,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1388])).

tff(c_1380,plain,(
    ! [A_17] : r1_tarski('#skF_5',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1378,c_22])).

tff(c_1391,plain,(
    ! [A_17] : r1_tarski('#skF_3',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_1380])).

tff(c_1377,plain,(
    ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1377])).

tff(c_1404,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1388])).

tff(c_1406,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1377])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.10/1.49  
% 3.10/1.49  %Foreground sorts:
% 3.10/1.49  
% 3.10/1.49  
% 3.10/1.49  %Background operators:
% 3.10/1.49  
% 3.10/1.49  
% 3.10/1.49  %Foreground operators:
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.10/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.10/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.10/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.10/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.49  
% 3.19/1.50  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.19/1.50  tff(f_93, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.19/1.50  tff(f_81, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.19/1.50  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.19/1.50  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.19/1.50  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.19/1.50  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.19/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.19/1.50  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.19/1.50  tff(f_63, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.19/1.50  tff(c_18, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.50  tff(c_48, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4')) | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.50  tff(c_69, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_48])).
% 3.19/1.50  tff(c_40, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), B_47) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.19/1.50  tff(c_44, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4')) | k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.50  tff(c_188, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_44])).
% 3.19/1.50  tff(c_54, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.50  tff(c_323, plain, (r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.19/1.50  tff(c_14, plain, (![B_14, A_13]: (B_14=A_13 | ~r1_tarski(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.50  tff(c_325, plain, (k1_tarski('#skF_6')='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_323, c_14])).
% 3.19/1.50  tff(c_331, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_188, c_325])).
% 3.19/1.50  tff(c_336, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_331])).
% 3.19/1.50  tff(c_42, plain, (![A_48, B_49]: (r1_xboole_0(k1_tarski(A_48), B_49) | r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.19/1.50  tff(c_20, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.50  tff(c_332, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_323, c_20])).
% 3.19/1.50  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.50  tff(c_279, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.50  tff(c_344, plain, (![A_87, B_88]: (~r1_xboole_0(A_87, B_88) | v1_xboole_0(k3_xboole_0(A_87, B_88)))), inference(resolution, [status(thm)], [c_6, c_279])).
% 3.19/1.50  tff(c_350, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_6')) | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_332, c_344])).
% 3.19/1.50  tff(c_428, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_350])).
% 3.19/1.50  tff(c_369, plain, (![A_89, B_90]: (r2_hidden('#skF_2'(A_89, B_90), k3_xboole_0(A_89, B_90)) | r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.50  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.50  tff(c_429, plain, (![A_94, B_95]: (~v1_xboole_0(k3_xboole_0(A_94, B_95)) | r1_xboole_0(A_94, B_95))), inference(resolution, [status(thm)], [c_369, c_4])).
% 3.19/1.50  tff(c_435, plain, (~v1_xboole_0('#skF_5') | r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_429])).
% 3.19/1.50  tff(c_452, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_428, c_435])).
% 3.19/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.50  tff(c_494, plain, (![A_103, B_104]: (~r1_xboole_0(A_103, B_104) | v1_xboole_0(k3_xboole_0(B_104, A_103)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_344])).
% 3.19/1.50  tff(c_503, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_332, c_494])).
% 3.19/1.50  tff(c_521, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_452, c_503])).
% 3.19/1.50  tff(c_528, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_521])).
% 3.19/1.50  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_528])).
% 3.19/1.50  tff(c_533, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_350])).
% 3.19/1.50  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.50  tff(c_537, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_533, c_8])).
% 3.19/1.50  tff(c_541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_537])).
% 3.19/1.50  tff(c_542, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_54])).
% 3.19/1.50  tff(c_544, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_542])).
% 3.19/1.50  tff(c_52, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4')) | r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.50  tff(c_235, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.19/1.50  tff(c_545, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_544, c_235])).
% 3.19/1.50  tff(c_548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_545])).
% 3.19/1.50  tff(c_549, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_542])).
% 3.19/1.50  tff(c_22, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.19/1.50  tff(c_558, plain, (![A_17]: (r1_tarski('#skF_3', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_22])).
% 3.19/1.50  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_558, c_235])).
% 3.19/1.50  tff(c_566, plain, (r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_52])).
% 3.19/1.50  tff(c_618, plain, (![B_109, A_110]: (B_109=A_110 | ~r1_tarski(B_109, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.50  tff(c_622, plain, (k1_tarski('#skF_6')='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_566, c_618])).
% 3.19/1.50  tff(c_632, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_188, c_622])).
% 3.19/1.50  tff(c_647, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_632])).
% 3.19/1.50  tff(c_571, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_566, c_20])).
% 3.19/1.50  tff(c_584, plain, (![A_105, B_106, C_107]: (~r1_xboole_0(A_105, B_106) | ~r2_hidden(C_107, k3_xboole_0(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.50  tff(c_673, plain, (![A_114, B_115]: (~r1_xboole_0(A_114, B_115) | v1_xboole_0(k3_xboole_0(A_114, B_115)))), inference(resolution, [status(thm)], [c_6, c_584])).
% 3.19/1.50  tff(c_682, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_6')) | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_571, c_673])).
% 3.19/1.50  tff(c_719, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_682])).
% 3.19/1.50  tff(c_939, plain, (![A_132, B_133]: (r2_hidden('#skF_2'(A_132, B_133), k3_xboole_0(A_132, B_133)) | r1_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.50  tff(c_948, plain, (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6')), '#skF_5') | r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_571, c_939])).
% 3.19/1.50  tff(c_966, plain, (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_719, c_948])).
% 3.19/1.50  tff(c_995, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_966, c_4])).
% 3.19/1.50  tff(c_1192, plain, (![B_153, A_154]: (~r1_xboole_0(B_153, A_154) | v1_xboole_0(k3_xboole_0(A_154, B_153)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_673])).
% 3.19/1.50  tff(c_1204, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_571, c_1192])).
% 3.19/1.50  tff(c_1223, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_995, c_1204])).
% 3.19/1.50  tff(c_1239, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_1223])).
% 3.19/1.50  tff(c_1243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_647, c_1239])).
% 3.19/1.50  tff(c_1244, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_682])).
% 3.19/1.50  tff(c_1248, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1244, c_8])).
% 3.19/1.50  tff(c_1252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_1248])).
% 3.19/1.50  tff(c_1254, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 3.19/1.50  tff(c_46, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.50  tff(c_1356, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_46])).
% 3.19/1.50  tff(c_1357, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1356])).
% 3.19/1.50  tff(c_1363, plain, (![A_17]: (r1_tarski('#skF_3', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_22])).
% 3.19/1.50  tff(c_1253, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 3.19/1.50  tff(c_1370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1363, c_1253])).
% 3.19/1.50  tff(c_1371, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1356])).
% 3.19/1.50  tff(c_1373, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1371, c_1253])).
% 3.19/1.50  tff(c_1376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1373])).
% 3.19/1.50  tff(c_1378, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 3.19/1.50  tff(c_50, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.50  tff(c_1388, plain, (k1_tarski('#skF_4')='#skF_3' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1378, c_1378, c_50])).
% 3.19/1.50  tff(c_1389, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_1388])).
% 3.19/1.50  tff(c_1380, plain, (![A_17]: (r1_tarski('#skF_5', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_1378, c_22])).
% 3.19/1.50  tff(c_1391, plain, (![A_17]: (r1_tarski('#skF_3', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_1380])).
% 3.19/1.50  tff(c_1377, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 3.19/1.50  tff(c_1403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1391, c_1377])).
% 3.19/1.50  tff(c_1404, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1388])).
% 3.19/1.50  tff(c_1406, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_1377])).
% 3.19/1.50  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1406])).
% 3.19/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  Inference rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Ref     : 0
% 3.19/1.50  #Sup     : 299
% 3.19/1.50  #Fact    : 0
% 3.19/1.50  #Define  : 0
% 3.19/1.50  #Split   : 16
% 3.19/1.50  #Chain   : 0
% 3.19/1.50  #Close   : 0
% 3.19/1.50  
% 3.19/1.50  Ordering : KBO
% 3.19/1.50  
% 3.19/1.50  Simplification rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Subsume      : 47
% 3.19/1.50  #Demod        : 132
% 3.19/1.50  #Tautology    : 148
% 3.19/1.50  #SimpNegUnit  : 27
% 3.19/1.50  #BackRed      : 36
% 3.19/1.50  
% 3.19/1.50  #Partial instantiations: 0
% 3.19/1.50  #Strategies tried      : 1
% 3.19/1.50  
% 3.19/1.50  Timing (in seconds)
% 3.19/1.50  ----------------------
% 3.19/1.51  Preprocessing        : 0.32
% 3.19/1.51  Parsing              : 0.17
% 3.19/1.51  CNF conversion       : 0.02
% 3.19/1.51  Main loop            : 0.41
% 3.19/1.51  Inferencing          : 0.15
% 3.19/1.51  Reduction            : 0.13
% 3.19/1.51  Demodulation         : 0.09
% 3.19/1.51  BG Simplification    : 0.03
% 3.19/1.51  Subsumption          : 0.07
% 3.19/1.51  Abstraction          : 0.02
% 3.19/1.51  MUC search           : 0.00
% 3.19/1.51  Cooper               : 0.00
% 3.19/1.51  Total                : 0.77
% 3.19/1.51  Index Insertion      : 0.00
% 3.19/1.51  Index Deletion       : 0.00
% 3.19/1.51  Index Matching       : 0.00
% 3.19/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
