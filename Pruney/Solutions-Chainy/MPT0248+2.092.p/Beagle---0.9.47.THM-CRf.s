%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:17 EST 2020

% Result     : Theorem 32.26s
% Output     : CNFRefutation 32.27s
% Verified   : 
% Statistics : Number of formulae       :  176 (1289 expanded)
%              Number of leaves         :   41 ( 447 expanded)
%              Depth                    :   22
%              Number of atoms          :  230 (1896 expanded)
%              Number of equality atoms :  102 (1540 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_80,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_128,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_74,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_78,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_127,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_130,plain,(
    ! [A_77,B_78] : r1_tarski(A_77,k2_xboole_0(A_77,B_78)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_133,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_130])).

tff(c_235,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_tarski(B_99,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_239,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_235])).

tff(c_251,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_239])).

tff(c_262,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_251])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_331,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_tarski(A_110,C_111)
      | ~ r1_tarski(B_112,C_111)
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_370,plain,(
    ! [A_115] :
      ( r1_tarski(A_115,k1_tarski('#skF_4'))
      | ~ r1_tarski(A_115,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_133,c_331])).

tff(c_72,plain,(
    ! [A_64,B_65] :
      ( r2_hidden(A_64,B_65)
      | ~ r1_tarski(k1_tarski(A_64),B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_499,plain,(
    ! [A_129] :
      ( r2_hidden(A_129,k1_tarski('#skF_4'))
      | ~ r1_tarski(k1_tarski(A_129),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_370,c_72])).

tff(c_46,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_603,plain,(
    ! [A_134] :
      ( A_134 = '#skF_4'
      | ~ r1_tarski(k1_tarski(A_134),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_499,c_46])).

tff(c_621,plain,(
    ! [A_136] :
      ( A_136 = '#skF_4'
      | ~ r2_hidden(A_136,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_603])).

tff(c_627,plain,(
    ! [B_137] :
      ( '#skF_1'('#skF_5',B_137) = '#skF_4'
      | r1_tarski('#skF_5',B_137) ) ),
    inference(resolution,[status(thm)],[c_6,c_621])).

tff(c_34,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_258,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_235])).

tff(c_640,plain,
    ( k1_xboole_0 = '#skF_5'
    | '#skF_1'('#skF_5',k1_xboole_0) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_627,c_258])).

tff(c_648,plain,(
    '#skF_1'('#skF_5',k1_xboole_0) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_640])).

tff(c_719,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_tarski('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_6])).

tff(c_725,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_719])).

tff(c_733,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_725,c_258])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_733])).

tff(c_742,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_743,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_42,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_744,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_42])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1054,plain,(
    ! [A_190,B_191] : k5_xboole_0(k5_xboole_0(A_190,B_191),k2_xboole_0(A_190,B_191)) = k3_xboole_0(A_190,B_191) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1085,plain,(
    ! [A_28] : k5_xboole_0('#skF_5',k2_xboole_0(A_28,A_28)) = k3_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_1054])).

tff(c_1094,plain,(
    ! [A_28] : k5_xboole_0('#skF_5',A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_1085])).

tff(c_40,plain,(
    ! [A_25,B_26,C_27] : k5_xboole_0(k5_xboole_0(A_25,B_26),C_27) = k5_xboole_0(A_25,k5_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_969,plain,(
    ! [A_181,B_182,C_183] : k5_xboole_0(k5_xboole_0(A_181,B_182),C_183) = k5_xboole_0(A_181,k5_xboole_0(B_182,C_183)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1243,plain,(
    ! [A_205,B_206] : k5_xboole_0(A_205,k5_xboole_0(B_206,k5_xboole_0(A_205,B_206))) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_969])).

tff(c_1326,plain,(
    ! [A_207] : k5_xboole_0(A_207,k5_xboole_0(A_207,'#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_1243])).

tff(c_1345,plain,(
    ! [A_207,C_27] : k5_xboole_0(A_207,k5_xboole_0(k5_xboole_0(A_207,'#skF_5'),C_27)) = k5_xboole_0('#skF_5',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_40])).

tff(c_1386,plain,(
    ! [A_208,C_209] : k5_xboole_0(A_208,k5_xboole_0(A_208,C_209)) = C_209 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1094,c_40,c_1345])).

tff(c_1456,plain,(
    ! [A_28] : k5_xboole_0(A_28,'#skF_5') = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_1386])).

tff(c_36,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_745,plain,(
    ! [A_20] : r1_tarski('#skF_5',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_34])).

tff(c_830,plain,(
    ! [B_162,A_163] :
      ( B_162 = A_163
      | ~ r1_tarski(B_162,A_163)
      | ~ r1_tarski(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_849,plain,(
    ! [A_164] :
      ( A_164 = '#skF_5'
      | ~ r1_tarski(A_164,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_745,c_830])).

tff(c_867,plain,(
    ! [B_22] : k4_xboole_0('#skF_5',B_22) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_849])).

tff(c_1096,plain,(
    ! [A_192] : k5_xboole_0('#skF_5',A_192) = A_192 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_1085])).

tff(c_30,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1109,plain,(
    ! [B_16] : k4_xboole_0('#skF_5',B_16) = k3_xboole_0('#skF_5',B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_30])).

tff(c_1127,plain,(
    ! [B_16] : k3_xboole_0('#skF_5',B_16) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_1109])).

tff(c_1088,plain,(
    k5_xboole_0(k5_xboole_0('#skF_5','#skF_6'),k1_tarski('#skF_4')) = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1054])).

tff(c_1310,plain,(
    k5_xboole_0('#skF_6',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_1094,c_1088])).

tff(c_1426,plain,(
    k5_xboole_0('#skF_6','#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_1386])).

tff(c_1525,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1426])).

tff(c_1526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_1525])).

tff(c_1527,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2621,plain,(
    ! [A_294,B_295] : k5_xboole_0(k5_xboole_0(A_294,B_295),k2_xboole_0(A_294,B_295)) = k3_xboole_0(A_294,B_295) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2682,plain,(
    ! [A_6] : k5_xboole_0(k5_xboole_0(A_6,A_6),A_6) = k3_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2621])).

tff(c_2688,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10,c_2682])).

tff(c_2188,plain,(
    ! [A_280,B_281,C_282] : k5_xboole_0(k5_xboole_0(A_280,B_281),C_282) = k5_xboole_0(A_280,k5_xboole_0(B_281,C_282)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2380,plain,(
    ! [A_289,C_290] : k5_xboole_0(A_289,k5_xboole_0(A_289,C_290)) = k5_xboole_0(k1_xboole_0,C_290) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2188])).

tff(c_2440,plain,(
    ! [A_28] : k5_xboole_0(k1_xboole_0,A_28) = k5_xboole_0(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2380])).

tff(c_2690,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2440])).

tff(c_2202,plain,(
    ! [A_280,B_281] : k5_xboole_0(A_280,k5_xboole_0(B_281,k5_xboole_0(A_280,B_281))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2188,c_42])).

tff(c_2218,plain,(
    ! [A_28,C_282] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_282)) = k5_xboole_0(k1_xboole_0,C_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2188])).

tff(c_2869,plain,(
    ! [A_299,C_300] : k5_xboole_0(A_299,k5_xboole_0(A_299,C_300)) = C_300 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2218])).

tff(c_2925,plain,(
    ! [B_281,A_280] : k5_xboole_0(B_281,k5_xboole_0(A_280,B_281)) = k5_xboole_0(A_280,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2202,c_2869])).

tff(c_2971,plain,(
    ! [B_305,A_306] : k5_xboole_0(B_305,k5_xboole_0(A_306,B_305)) = A_306 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2690,c_2925])).

tff(c_2956,plain,(
    ! [B_281,A_280] : k5_xboole_0(B_281,k5_xboole_0(A_280,B_281)) = A_280 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2690,c_2925])).

tff(c_2974,plain,(
    ! [A_306,B_305] : k5_xboole_0(k5_xboole_0(A_306,B_305),A_306) = B_305 ),
    inference(superposition,[status(thm),theory(equality)],[c_2971,c_2956])).

tff(c_1528,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1529,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_84])).

tff(c_2679,plain,(
    k5_xboole_0(k5_xboole_0('#skF_5','#skF_6'),'#skF_5') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_2621])).

tff(c_3052,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2679])).

tff(c_82,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1554,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1528,c_82])).

tff(c_48,plain,(
    ! [C_35] : r2_hidden(C_35,k1_tarski(C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1533,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1528,c_48])).

tff(c_3014,plain,(
    k5_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_6')) = k5_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2679,c_2971])).

tff(c_3047,plain,(
    k5_xboole_0('#skF_5','#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3014])).

tff(c_1579,plain,(
    ! [A_220,B_221] :
      ( r2_hidden(A_220,B_221)
      | ~ r1_tarski(k1_tarski(A_220),B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1586,plain,(
    ! [B_221] :
      ( r2_hidden('#skF_4',B_221)
      | ~ r1_tarski('#skF_5',B_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1528,c_1579])).

tff(c_3829,plain,(
    ! [A_323,C_324,B_325] :
      ( ~ r2_hidden(A_323,C_324)
      | ~ r2_hidden(A_323,B_325)
      | ~ r2_hidden(A_323,k5_xboole_0(B_325,C_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4277,plain,(
    ! [C_339,B_340] :
      ( ~ r2_hidden('#skF_4',C_339)
      | ~ r2_hidden('#skF_4',B_340)
      | ~ r1_tarski('#skF_5',k5_xboole_0(B_340,C_339)) ) ),
    inference(resolution,[status(thm)],[c_1586,c_3829])).

tff(c_4310,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_5',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3047,c_4277])).

tff(c_4353,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_5',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_4310])).

tff(c_4588,plain,(
    ~ r1_tarski('#skF_5',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4353])).

tff(c_1697,plain,(
    ! [A_233,B_234] :
      ( r2_hidden('#skF_1'(A_233,B_234),A_233)
      | r1_tarski(A_233,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1555,plain,(
    ! [C_215,A_216] :
      ( C_215 = A_216
      | ~ r2_hidden(C_215,k1_tarski(A_216)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1558,plain,(
    ! [C_215] :
      ( C_215 = '#skF_4'
      | ~ r2_hidden(C_215,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1528,c_1555])).

tff(c_1706,plain,(
    ! [B_234] :
      ( '#skF_1'('#skF_5',B_234) = '#skF_4'
      | r1_tarski('#skF_5',B_234) ) ),
    inference(resolution,[status(thm)],[c_1697,c_1558])).

tff(c_4625,plain,(
    '#skF_1'('#skF_5',k4_xboole_0('#skF_5','#skF_6')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1706,c_4588])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4629,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5','#skF_6'))
    | r1_tarski('#skF_5',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4625,c_4])).

tff(c_4635,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_4588,c_4629])).

tff(c_2692,plain,(
    ! [A_28,C_282] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_282)) = C_282 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2218])).

tff(c_3147,plain,(
    k5_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3047,c_2692])).

tff(c_4184,plain,(
    ! [A_334,C_335,B_336] :
      ( r2_hidden(A_334,C_335)
      | ~ r2_hidden(A_334,B_336)
      | r2_hidden(A_334,k5_xboole_0(B_336,C_335)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1662,plain,(
    ! [A_230,B_231] :
      ( r1_tarski(k1_tarski(A_230),B_231)
      | ~ r2_hidden(A_230,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1668,plain,(
    ! [B_231] :
      ( r1_tarski('#skF_5',B_231)
      | ~ r2_hidden('#skF_4',B_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1528,c_1662])).

tff(c_5098,plain,(
    ! [B_358,C_359] :
      ( r1_tarski('#skF_5',k5_xboole_0(B_358,C_359))
      | r2_hidden('#skF_4',C_359)
      | ~ r2_hidden('#skF_4',B_358) ) ),
    inference(resolution,[status(thm)],[c_4184,c_1668])).

tff(c_5143,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | r2_hidden('#skF_4',k4_xboole_0('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3147,c_5098])).

tff(c_5198,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | r2_hidden('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_5143])).

tff(c_5199,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_4635,c_5198])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | ~ r1_tarski(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5219,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_5199,c_24])).

tff(c_5226,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1554,c_5219])).

tff(c_3144,plain,(
    k5_xboole_0('#skF_6',k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3047,c_2956])).

tff(c_2980,plain,(
    ! [B_305,A_306] : k5_xboole_0(B_305,A_306) = k5_xboole_0(A_306,B_305) ),
    inference(superposition,[status(thm),theory(equality)],[c_2971,c_2692])).

tff(c_3158,plain,(
    ! [A_309,C_310] : k5_xboole_0(k5_xboole_0(A_309,C_310),C_310) = A_309 ),
    inference(superposition,[status(thm),theory(equality)],[c_2692,c_2971])).

tff(c_3199,plain,(
    k5_xboole_0(k4_xboole_0('#skF_5','#skF_6'),'#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3047,c_3158])).

tff(c_3680,plain,(
    ! [A_318,B_319,C_320] :
      ( r2_hidden(A_318,B_319)
      | ~ r2_hidden(A_318,C_320)
      | r2_hidden(A_318,k5_xboole_0(B_319,C_320)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63143,plain,(
    ! [A_15680,B_15681,C_15682] :
      ( r1_tarski(A_15680,k5_xboole_0(B_15681,C_15682))
      | r2_hidden('#skF_1'(A_15680,k5_xboole_0(B_15681,C_15682)),B_15681)
      | ~ r2_hidden('#skF_1'(A_15680,k5_xboole_0(B_15681,C_15682)),C_15682) ) ),
    inference(resolution,[status(thm)],[c_3680,c_4])).

tff(c_112411,plain,(
    ! [A_15900,B_15901] :
      ( r2_hidden('#skF_1'(A_15900,k5_xboole_0(B_15901,A_15900)),B_15901)
      | r1_tarski(A_15900,k5_xboole_0(B_15901,A_15900)) ) ),
    inference(resolution,[status(thm)],[c_6,c_63143])).

tff(c_112790,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_5'),k4_xboole_0('#skF_5','#skF_6'))
    | r1_tarski('#skF_6',k5_xboole_0(k4_xboole_0('#skF_5','#skF_6'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3199,c_112411])).

tff(c_112961,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_5'),k4_xboole_0('#skF_5','#skF_6'))
    | r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3144,c_2980,c_112790])).

tff(c_112962,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_5'),k4_xboole_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_5226,c_112961])).

tff(c_1971,plain,(
    ! [A_257,C_258,B_259] :
      ( r1_tarski(A_257,C_258)
      | ~ r1_tarski(B_259,C_258)
      | ~ r1_tarski(A_257,B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2070,plain,(
    ! [A_269,A_270,B_271] :
      ( r1_tarski(A_269,A_270)
      | ~ r1_tarski(A_269,k4_xboole_0(A_270,B_271)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1971])).

tff(c_2103,plain,(
    ! [A_64,A_270,B_271] :
      ( r1_tarski(k1_tarski(A_64),A_270)
      | ~ r2_hidden(A_64,k4_xboole_0(A_270,B_271)) ) ),
    inference(resolution,[status(thm)],[c_74,c_2070])).

tff(c_113037,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_6','#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_112962,c_2103])).

tff(c_113285,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113037,c_72])).

tff(c_113298,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_113285,c_4])).

tff(c_113309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5226,c_113298])).

tff(c_113311,plain,(
    r1_tarski('#skF_5',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4353])).

tff(c_113382,plain,
    ( k4_xboole_0('#skF_5','#skF_6') = '#skF_5'
    | ~ r1_tarski(k4_xboole_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113311,c_24])).

tff(c_113393,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_113382])).

tff(c_2939,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2869])).

tff(c_113414,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_113393,c_2939])).

tff(c_113430,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3052,c_113414])).

tff(c_113432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1527,c_113430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n018.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 14:22:26 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.26/21.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.27/21.94  
% 32.27/21.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.27/21.94  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 32.27/21.94  
% 32.27/21.94  %Foreground sorts:
% 32.27/21.94  
% 32.27/21.94  
% 32.27/21.94  %Background operators:
% 32.27/21.94  
% 32.27/21.94  
% 32.27/21.94  %Foreground operators:
% 32.27/21.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.27/21.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.27/21.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 32.27/21.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 32.27/21.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 32.27/21.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 32.27/21.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 32.27/21.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 32.27/21.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.27/21.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 32.27/21.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 32.27/21.94  tff('#skF_5', type, '#skF_5': $i).
% 32.27/21.94  tff('#skF_6', type, '#skF_6': $i).
% 32.27/21.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 32.27/21.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 32.27/21.94  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 32.27/21.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.27/21.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 32.27/21.94  tff('#skF_4', type, '#skF_4': $i).
% 32.27/21.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.27/21.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 32.27/21.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 32.27/21.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 32.27/21.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 32.27/21.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 32.27/21.94  
% 32.27/21.97  tff(f_115, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 32.27/21.97  tff(f_94, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 32.27/21.97  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 32.27/21.97  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.27/21.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 32.27/21.97  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 32.27/21.97  tff(f_76, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 32.27/21.97  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 32.27/21.97  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 32.27/21.97  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 32.27/21.97  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 32.27/21.97  tff(f_69, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 32.27/21.97  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 32.27/21.97  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 32.27/21.97  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 32.27/21.97  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 32.27/21.97  tff(c_80, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_115])).
% 32.27/21.97  tff(c_128, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_80])).
% 32.27/21.97  tff(c_74, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_94])).
% 32.27/21.97  tff(c_78, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_115])).
% 32.27/21.97  tff(c_127, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_78])).
% 32.27/21.97  tff(c_84, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 32.27/21.97  tff(c_130, plain, (![A_77, B_78]: (r1_tarski(A_77, k2_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 32.27/21.97  tff(c_133, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_130])).
% 32.27/21.97  tff(c_235, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_tarski(B_99, A_100) | ~r1_tarski(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.27/21.97  tff(c_239, plain, (k1_tarski('#skF_4')='#skF_5' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_133, c_235])).
% 32.27/21.97  tff(c_251, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_127, c_239])).
% 32.27/21.97  tff(c_262, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_251])).
% 32.27/21.97  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.27/21.97  tff(c_331, plain, (![A_110, C_111, B_112]: (r1_tarski(A_110, C_111) | ~r1_tarski(B_112, C_111) | ~r1_tarski(A_110, B_112))), inference(cnfTransformation, [status(thm)], [f_57])).
% 32.27/21.97  tff(c_370, plain, (![A_115]: (r1_tarski(A_115, k1_tarski('#skF_4')) | ~r1_tarski(A_115, '#skF_5'))), inference(resolution, [status(thm)], [c_133, c_331])).
% 32.27/21.97  tff(c_72, plain, (![A_64, B_65]: (r2_hidden(A_64, B_65) | ~r1_tarski(k1_tarski(A_64), B_65))), inference(cnfTransformation, [status(thm)], [f_94])).
% 32.27/21.97  tff(c_499, plain, (![A_129]: (r2_hidden(A_129, k1_tarski('#skF_4')) | ~r1_tarski(k1_tarski(A_129), '#skF_5'))), inference(resolution, [status(thm)], [c_370, c_72])).
% 32.27/21.97  tff(c_46, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 32.27/21.97  tff(c_603, plain, (![A_134]: (A_134='#skF_4' | ~r1_tarski(k1_tarski(A_134), '#skF_5'))), inference(resolution, [status(thm)], [c_499, c_46])).
% 32.27/21.97  tff(c_621, plain, (![A_136]: (A_136='#skF_4' | ~r2_hidden(A_136, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_603])).
% 32.27/21.97  tff(c_627, plain, (![B_137]: ('#skF_1'('#skF_5', B_137)='#skF_4' | r1_tarski('#skF_5', B_137))), inference(resolution, [status(thm)], [c_6, c_621])).
% 32.27/21.97  tff(c_34, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 32.27/21.97  tff(c_258, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_235])).
% 32.27/21.97  tff(c_640, plain, (k1_xboole_0='#skF_5' | '#skF_1'('#skF_5', k1_xboole_0)='#skF_4'), inference(resolution, [status(thm)], [c_627, c_258])).
% 32.27/21.97  tff(c_648, plain, ('#skF_1'('#skF_5', k1_xboole_0)='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_128, c_640])).
% 32.27/21.97  tff(c_719, plain, (r2_hidden('#skF_4', '#skF_5') | r1_tarski('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_648, c_6])).
% 32.27/21.97  tff(c_725, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_262, c_719])).
% 32.27/21.97  tff(c_733, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_725, c_258])).
% 32.27/21.97  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_733])).
% 32.27/21.97  tff(c_742, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_80])).
% 32.27/21.97  tff(c_743, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_80])).
% 32.27/21.97  tff(c_42, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 32.27/21.97  tff(c_744, plain, (![A_28]: (k5_xboole_0(A_28, A_28)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_743, c_42])).
% 32.27/21.97  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 32.27/21.97  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 32.27/21.97  tff(c_1054, plain, (![A_190, B_191]: (k5_xboole_0(k5_xboole_0(A_190, B_191), k2_xboole_0(A_190, B_191))=k3_xboole_0(A_190, B_191))), inference(cnfTransformation, [status(thm)], [f_69])).
% 32.27/21.97  tff(c_1085, plain, (![A_28]: (k5_xboole_0('#skF_5', k2_xboole_0(A_28, A_28))=k3_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_744, c_1054])).
% 32.27/21.97  tff(c_1094, plain, (![A_28]: (k5_xboole_0('#skF_5', A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_1085])).
% 32.27/21.97  tff(c_40, plain, (![A_25, B_26, C_27]: (k5_xboole_0(k5_xboole_0(A_25, B_26), C_27)=k5_xboole_0(A_25, k5_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 32.27/21.97  tff(c_969, plain, (![A_181, B_182, C_183]: (k5_xboole_0(k5_xboole_0(A_181, B_182), C_183)=k5_xboole_0(A_181, k5_xboole_0(B_182, C_183)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 32.27/21.97  tff(c_1243, plain, (![A_205, B_206]: (k5_xboole_0(A_205, k5_xboole_0(B_206, k5_xboole_0(A_205, B_206)))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_744, c_969])).
% 32.27/21.97  tff(c_1326, plain, (![A_207]: (k5_xboole_0(A_207, k5_xboole_0(A_207, '#skF_5'))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1094, c_1243])).
% 32.27/21.97  tff(c_1345, plain, (![A_207, C_27]: (k5_xboole_0(A_207, k5_xboole_0(k5_xboole_0(A_207, '#skF_5'), C_27))=k5_xboole_0('#skF_5', C_27))), inference(superposition, [status(thm), theory('equality')], [c_1326, c_40])).
% 32.27/21.97  tff(c_1386, plain, (![A_208, C_209]: (k5_xboole_0(A_208, k5_xboole_0(A_208, C_209))=C_209)), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1094, c_40, c_1345])).
% 32.27/21.97  tff(c_1456, plain, (![A_28]: (k5_xboole_0(A_28, '#skF_5')=A_28)), inference(superposition, [status(thm), theory('equality')], [c_744, c_1386])).
% 32.27/21.97  tff(c_36, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 32.27/21.97  tff(c_745, plain, (![A_20]: (r1_tarski('#skF_5', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_743, c_34])).
% 32.27/21.97  tff(c_830, plain, (![B_162, A_163]: (B_162=A_163 | ~r1_tarski(B_162, A_163) | ~r1_tarski(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.27/21.97  tff(c_849, plain, (![A_164]: (A_164='#skF_5' | ~r1_tarski(A_164, '#skF_5'))), inference(resolution, [status(thm)], [c_745, c_830])).
% 32.27/21.97  tff(c_867, plain, (![B_22]: (k4_xboole_0('#skF_5', B_22)='#skF_5')), inference(resolution, [status(thm)], [c_36, c_849])).
% 32.27/21.97  tff(c_1096, plain, (![A_192]: (k5_xboole_0('#skF_5', A_192)=A_192)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_1085])).
% 32.27/21.97  tff(c_30, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 32.27/21.97  tff(c_1109, plain, (![B_16]: (k4_xboole_0('#skF_5', B_16)=k3_xboole_0('#skF_5', B_16))), inference(superposition, [status(thm), theory('equality')], [c_1096, c_30])).
% 32.27/21.97  tff(c_1127, plain, (![B_16]: (k3_xboole_0('#skF_5', B_16)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_867, c_1109])).
% 32.27/21.97  tff(c_1088, plain, (k5_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), k1_tarski('#skF_4'))=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_84, c_1054])).
% 32.27/21.97  tff(c_1310, plain, (k5_xboole_0('#skF_6', k1_tarski('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_1094, c_1088])).
% 32.27/21.97  tff(c_1426, plain, (k5_xboole_0('#skF_6', '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1310, c_1386])).
% 32.27/21.97  tff(c_1525, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_1426])).
% 32.27/21.97  tff(c_1526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_742, c_1525])).
% 32.27/21.97  tff(c_1527, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_78])).
% 32.27/21.97  tff(c_2621, plain, (![A_294, B_295]: (k5_xboole_0(k5_xboole_0(A_294, B_295), k2_xboole_0(A_294, B_295))=k3_xboole_0(A_294, B_295))), inference(cnfTransformation, [status(thm)], [f_69])).
% 32.27/21.97  tff(c_2682, plain, (![A_6]: (k5_xboole_0(k5_xboole_0(A_6, A_6), A_6)=k3_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2621])).
% 32.27/21.97  tff(c_2688, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10, c_2682])).
% 32.27/21.97  tff(c_2188, plain, (![A_280, B_281, C_282]: (k5_xboole_0(k5_xboole_0(A_280, B_281), C_282)=k5_xboole_0(A_280, k5_xboole_0(B_281, C_282)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 32.27/21.97  tff(c_2380, plain, (![A_289, C_290]: (k5_xboole_0(A_289, k5_xboole_0(A_289, C_290))=k5_xboole_0(k1_xboole_0, C_290))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2188])).
% 32.27/21.97  tff(c_2440, plain, (![A_28]: (k5_xboole_0(k1_xboole_0, A_28)=k5_xboole_0(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2380])).
% 32.27/21.97  tff(c_2690, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2440])).
% 32.27/21.97  tff(c_2202, plain, (![A_280, B_281]: (k5_xboole_0(A_280, k5_xboole_0(B_281, k5_xboole_0(A_280, B_281)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2188, c_42])).
% 32.27/21.97  tff(c_2218, plain, (![A_28, C_282]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_282))=k5_xboole_0(k1_xboole_0, C_282))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2188])).
% 32.27/21.97  tff(c_2869, plain, (![A_299, C_300]: (k5_xboole_0(A_299, k5_xboole_0(A_299, C_300))=C_300)), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2218])).
% 32.27/21.97  tff(c_2925, plain, (![B_281, A_280]: (k5_xboole_0(B_281, k5_xboole_0(A_280, B_281))=k5_xboole_0(A_280, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2202, c_2869])).
% 32.27/21.97  tff(c_2971, plain, (![B_305, A_306]: (k5_xboole_0(B_305, k5_xboole_0(A_306, B_305))=A_306)), inference(demodulation, [status(thm), theory('equality')], [c_2690, c_2925])).
% 32.27/21.97  tff(c_2956, plain, (![B_281, A_280]: (k5_xboole_0(B_281, k5_xboole_0(A_280, B_281))=A_280)), inference(demodulation, [status(thm), theory('equality')], [c_2690, c_2925])).
% 32.27/21.97  tff(c_2974, plain, (![A_306, B_305]: (k5_xboole_0(k5_xboole_0(A_306, B_305), A_306)=B_305)), inference(superposition, [status(thm), theory('equality')], [c_2971, c_2956])).
% 32.27/21.97  tff(c_1528, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_78])).
% 32.27/21.97  tff(c_1529, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_84])).
% 32.27/21.97  tff(c_2679, plain, (k5_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), '#skF_5')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1529, c_2621])).
% 32.27/21.97  tff(c_3052, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2679])).
% 32.27/21.97  tff(c_82, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_115])).
% 32.27/21.97  tff(c_1554, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1528, c_82])).
% 32.27/21.97  tff(c_48, plain, (![C_35]: (r2_hidden(C_35, k1_tarski(C_35)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 32.27/21.97  tff(c_1533, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1528, c_48])).
% 32.27/21.97  tff(c_3014, plain, (k5_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2679, c_2971])).
% 32.27/21.97  tff(c_3047, plain, (k5_xboole_0('#skF_5', '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3014])).
% 32.27/21.97  tff(c_1579, plain, (![A_220, B_221]: (r2_hidden(A_220, B_221) | ~r1_tarski(k1_tarski(A_220), B_221))), inference(cnfTransformation, [status(thm)], [f_94])).
% 32.27/21.97  tff(c_1586, plain, (![B_221]: (r2_hidden('#skF_4', B_221) | ~r1_tarski('#skF_5', B_221))), inference(superposition, [status(thm), theory('equality')], [c_1528, c_1579])).
% 32.27/21.97  tff(c_3829, plain, (![A_323, C_324, B_325]: (~r2_hidden(A_323, C_324) | ~r2_hidden(A_323, B_325) | ~r2_hidden(A_323, k5_xboole_0(B_325, C_324)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.27/21.97  tff(c_4277, plain, (![C_339, B_340]: (~r2_hidden('#skF_4', C_339) | ~r2_hidden('#skF_4', B_340) | ~r1_tarski('#skF_5', k5_xboole_0(B_340, C_339)))), inference(resolution, [status(thm)], [c_1586, c_3829])).
% 32.27/21.97  tff(c_4310, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_4', '#skF_5') | ~r1_tarski('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3047, c_4277])).
% 32.27/21.97  tff(c_4353, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r1_tarski('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_4310])).
% 32.27/21.97  tff(c_4588, plain, (~r1_tarski('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_4353])).
% 32.27/21.97  tff(c_1697, plain, (![A_233, B_234]: (r2_hidden('#skF_1'(A_233, B_234), A_233) | r1_tarski(A_233, B_234))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.27/21.97  tff(c_1555, plain, (![C_215, A_216]: (C_215=A_216 | ~r2_hidden(C_215, k1_tarski(A_216)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 32.27/21.97  tff(c_1558, plain, (![C_215]: (C_215='#skF_4' | ~r2_hidden(C_215, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1528, c_1555])).
% 32.27/21.97  tff(c_1706, plain, (![B_234]: ('#skF_1'('#skF_5', B_234)='#skF_4' | r1_tarski('#skF_5', B_234))), inference(resolution, [status(thm)], [c_1697, c_1558])).
% 32.27/21.97  tff(c_4625, plain, ('#skF_1'('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))='#skF_4'), inference(resolution, [status(thm)], [c_1706, c_4588])).
% 32.27/21.97  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.27/21.97  tff(c_4629, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', '#skF_6')) | r1_tarski('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4625, c_4])).
% 32.27/21.97  tff(c_4635, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_4588, c_4629])).
% 32.27/21.97  tff(c_2692, plain, (![A_28, C_282]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_282))=C_282)), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2218])).
% 32.27/21.97  tff(c_3147, plain, (k5_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3047, c_2692])).
% 32.27/21.97  tff(c_4184, plain, (![A_334, C_335, B_336]: (r2_hidden(A_334, C_335) | ~r2_hidden(A_334, B_336) | r2_hidden(A_334, k5_xboole_0(B_336, C_335)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.27/21.97  tff(c_1662, plain, (![A_230, B_231]: (r1_tarski(k1_tarski(A_230), B_231) | ~r2_hidden(A_230, B_231))), inference(cnfTransformation, [status(thm)], [f_94])).
% 32.27/21.97  tff(c_1668, plain, (![B_231]: (r1_tarski('#skF_5', B_231) | ~r2_hidden('#skF_4', B_231))), inference(superposition, [status(thm), theory('equality')], [c_1528, c_1662])).
% 32.27/21.97  tff(c_5098, plain, (![B_358, C_359]: (r1_tarski('#skF_5', k5_xboole_0(B_358, C_359)) | r2_hidden('#skF_4', C_359) | ~r2_hidden('#skF_4', B_358))), inference(resolution, [status(thm)], [c_4184, c_1668])).
% 32.27/21.97  tff(c_5143, plain, (r1_tarski('#skF_5', '#skF_6') | r2_hidden('#skF_4', k4_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3147, c_5098])).
% 32.27/21.97  tff(c_5198, plain, (r1_tarski('#skF_5', '#skF_6') | r2_hidden('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_5143])).
% 32.27/21.97  tff(c_5199, plain, (r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_4635, c_5198])).
% 32.27/21.97  tff(c_24, plain, (![B_14, A_13]: (B_14=A_13 | ~r1_tarski(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.27/21.97  tff(c_5219, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_5199, c_24])).
% 32.27/21.97  tff(c_5226, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1554, c_5219])).
% 32.27/21.97  tff(c_3144, plain, (k5_xboole_0('#skF_6', k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3047, c_2956])).
% 32.27/21.97  tff(c_2980, plain, (![B_305, A_306]: (k5_xboole_0(B_305, A_306)=k5_xboole_0(A_306, B_305))), inference(superposition, [status(thm), theory('equality')], [c_2971, c_2692])).
% 32.27/21.97  tff(c_3158, plain, (![A_309, C_310]: (k5_xboole_0(k5_xboole_0(A_309, C_310), C_310)=A_309)), inference(superposition, [status(thm), theory('equality')], [c_2692, c_2971])).
% 32.27/21.97  tff(c_3199, plain, (k5_xboole_0(k4_xboole_0('#skF_5', '#skF_6'), '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3047, c_3158])).
% 32.27/21.97  tff(c_3680, plain, (![A_318, B_319, C_320]: (r2_hidden(A_318, B_319) | ~r2_hidden(A_318, C_320) | r2_hidden(A_318, k5_xboole_0(B_319, C_320)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.27/21.97  tff(c_63143, plain, (![A_15680, B_15681, C_15682]: (r1_tarski(A_15680, k5_xboole_0(B_15681, C_15682)) | r2_hidden('#skF_1'(A_15680, k5_xboole_0(B_15681, C_15682)), B_15681) | ~r2_hidden('#skF_1'(A_15680, k5_xboole_0(B_15681, C_15682)), C_15682))), inference(resolution, [status(thm)], [c_3680, c_4])).
% 32.27/21.97  tff(c_112411, plain, (![A_15900, B_15901]: (r2_hidden('#skF_1'(A_15900, k5_xboole_0(B_15901, A_15900)), B_15901) | r1_tarski(A_15900, k5_xboole_0(B_15901, A_15900)))), inference(resolution, [status(thm)], [c_6, c_63143])).
% 32.27/21.97  tff(c_112790, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), k4_xboole_0('#skF_5', '#skF_6')) | r1_tarski('#skF_6', k5_xboole_0(k4_xboole_0('#skF_5', '#skF_6'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3199, c_112411])).
% 32.27/21.97  tff(c_112961, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), k4_xboole_0('#skF_5', '#skF_6')) | r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3144, c_2980, c_112790])).
% 32.27/21.97  tff(c_112962, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), k4_xboole_0('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_5226, c_112961])).
% 32.27/21.97  tff(c_1971, plain, (![A_257, C_258, B_259]: (r1_tarski(A_257, C_258) | ~r1_tarski(B_259, C_258) | ~r1_tarski(A_257, B_259))), inference(cnfTransformation, [status(thm)], [f_57])).
% 32.27/21.97  tff(c_2070, plain, (![A_269, A_270, B_271]: (r1_tarski(A_269, A_270) | ~r1_tarski(A_269, k4_xboole_0(A_270, B_271)))), inference(resolution, [status(thm)], [c_36, c_1971])).
% 32.27/21.97  tff(c_2103, plain, (![A_64, A_270, B_271]: (r1_tarski(k1_tarski(A_64), A_270) | ~r2_hidden(A_64, k4_xboole_0(A_270, B_271)))), inference(resolution, [status(thm)], [c_74, c_2070])).
% 32.27/21.97  tff(c_113037, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_6', '#skF_5')), '#skF_5')), inference(resolution, [status(thm)], [c_112962, c_2103])).
% 32.27/21.97  tff(c_113285, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113037, c_72])).
% 32.27/21.97  tff(c_113298, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_113285, c_4])).
% 32.27/21.97  tff(c_113309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5226, c_113298])).
% 32.27/21.97  tff(c_113311, plain, (r1_tarski('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_4353])).
% 32.27/21.97  tff(c_113382, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5' | ~r1_tarski(k4_xboole_0('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_113311, c_24])).
% 32.27/21.97  tff(c_113393, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_113382])).
% 32.27/21.97  tff(c_2939, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2869])).
% 32.27/21.97  tff(c_113414, plain, (k5_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_113393, c_2939])).
% 32.27/21.97  tff(c_113430, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3052, c_113414])).
% 32.27/21.97  tff(c_113432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1527, c_113430])).
% 32.27/21.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.27/21.97  
% 32.27/21.97  Inference rules
% 32.27/21.97  ----------------------
% 32.27/21.97  #Ref     : 0
% 32.27/21.97  #Sup     : 26372
% 32.27/21.97  #Fact    : 6
% 32.27/21.97  #Define  : 0
% 32.27/21.97  #Split   : 6
% 32.27/21.97  #Chain   : 0
% 32.27/21.97  #Close   : 0
% 32.27/21.97  
% 32.27/21.97  Ordering : KBO
% 32.27/21.97  
% 32.27/21.97  Simplification rules
% 32.27/21.97  ----------------------
% 32.27/21.97  #Subsume      : 3814
% 32.27/21.97  #Demod        : 34746
% 32.27/21.97  #Tautology    : 6541
% 32.27/21.97  #SimpNegUnit  : 263
% 32.27/21.97  #BackRed      : 27
% 32.27/21.97  
% 32.27/21.97  #Partial instantiations: 5840
% 32.27/21.97  #Strategies tried      : 1
% 32.27/21.97  
% 32.27/21.97  Timing (in seconds)
% 32.27/21.97  ----------------------
% 32.27/21.97  Preprocessing        : 0.35
% 32.27/21.97  Parsing              : 0.19
% 32.27/21.97  CNF conversion       : 0.03
% 32.27/21.97  Main loop            : 20.90
% 32.27/21.97  Inferencing          : 2.41
% 32.27/21.97  Reduction            : 13.51
% 32.27/21.97  Demodulation         : 12.57
% 32.27/21.97  BG Simplification    : 0.41
% 32.27/21.97  Subsumption          : 3.78
% 32.27/21.97  Abstraction          : 0.60
% 32.27/21.97  MUC search           : 0.00
% 32.27/21.97  Cooper               : 0.00
% 32.27/21.97  Total                : 21.31
% 32.27/21.97  Index Insertion      : 0.00
% 32.27/21.97  Index Deletion       : 0.00
% 32.27/21.97  Index Matching       : 0.00
% 32.27/21.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
