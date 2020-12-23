%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:12 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 350 expanded)
%              Number of leaves         :   42 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          :  158 ( 637 expanded)
%              Number of equality atoms :   59 ( 385 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

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

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_75,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_58,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_99,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_85,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1068,plain,(
    ! [B_136,A_137] :
      ( k3_xboole_0(B_136,k1_tarski(A_137)) = k1_tarski(A_137)
      | ~ r2_hidden(A_137,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_62,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_95,plain,(
    ! [A_73,B_74] : r1_tarski(A_73,k2_xboole_0(A_73,B_74)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_98,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_95])).

tff(c_199,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_213,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_98,c_199])).

tff(c_1093,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_213])).

tff(c_1129,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1093])).

tff(c_50,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),B_62)
      | r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_714,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ r1_xboole_0(A_115,B_116)
      | ~ r2_hidden(C_117,k3_xboole_0(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_723,plain,(
    ! [C_117] :
      ( ~ r1_xboole_0('#skF_4',k1_tarski('#skF_3'))
      | ~ r2_hidden(C_117,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_714])).

tff(c_744,plain,(
    ~ r1_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_1657,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_2'(A_156,B_157),k3_xboole_0(A_156,B_157))
      | r1_xboole_0(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1684,plain,
    ( r2_hidden('#skF_2'('#skF_4',k1_tarski('#skF_3')),'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_1657])).

tff(c_1693,plain,(
    r2_hidden('#skF_2'('#skF_4',k1_tarski('#skF_3')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_1684])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1697,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1693,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2284,plain,(
    ! [A_183,B_184] :
      ( ~ r1_xboole_0(A_183,B_184)
      | v1_xboole_0(k3_xboole_0(A_183,B_184)) ) ),
    inference(resolution,[status(thm)],[c_6,c_714])).

tff(c_2524,plain,(
    ! [B_202,A_203] :
      ( ~ r1_xboole_0(B_202,A_203)
      | v1_xboole_0(k3_xboole_0(A_203,B_202)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2284])).

tff(c_2557,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_2524])).

tff(c_2567,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1697,c_2557])).

tff(c_2570,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2567])).

tff(c_2574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1129,c_2570])).

tff(c_2577,plain,(
    ! [C_204] : ~ r2_hidden(C_204,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_2582,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2577])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2585,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2582,c_8])).

tff(c_2589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2585])).

tff(c_2590,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_34,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2591,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2827,plain,(
    ! [A_229,B_230] :
      ( k4_xboole_0(A_229,B_230) = '#skF_4'
      | ~ r1_tarski(A_229,B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2591,c_16])).

tff(c_2915,plain,(
    ! [A_235,B_236] : k4_xboole_0(A_235,k2_xboole_0(A_235,B_236)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_2827])).

tff(c_30,plain,(
    ! [A_28,B_29] : r1_tarski(k4_xboole_0(A_28,B_29),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2925,plain,(
    ! [A_235] : r1_tarski('#skF_4',A_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_2915,c_30])).

tff(c_2951,plain,(
    ! [A_238,B_239] :
      ( k2_xboole_0(A_238,B_239) = B_239
      | ~ r1_tarski(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2967,plain,(
    ! [A_235] : k2_xboole_0('#skF_4',A_235) = A_235 ),
    inference(resolution,[status(thm)],[c_2925,c_2951])).

tff(c_2998,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2967,c_62])).

tff(c_3000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2590,c_2998])).

tff(c_3001,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_32,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    ! [A_27] : k3_xboole_0(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3463,plain,(
    ! [A_273,B_274] : k5_xboole_0(A_273,k3_xboole_0(A_273,B_274)) = k4_xboole_0(A_273,B_274) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3493,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = k4_xboole_0(A_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3463])).

tff(c_3500,plain,(
    ! [A_275] : k4_xboole_0(A_275,k1_xboole_0) = A_275 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3493])).

tff(c_3509,plain,(
    ! [A_275] : r1_tarski(A_275,A_275) ),
    inference(superposition,[status(thm),theory(equality)],[c_3500,c_30])).

tff(c_3002,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3004,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_62])).

tff(c_3765,plain,(
    ! [A_287,C_288,B_289] :
      ( r1_tarski(A_287,k2_xboole_0(C_288,B_289))
      | ~ r1_tarski(A_287,B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3793,plain,(
    ! [A_290] :
      ( r1_tarski(A_290,'#skF_4')
      | ~ r1_tarski(A_290,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3004,c_3765])).

tff(c_3812,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3509,c_3793])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3825,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3812,c_26])).

tff(c_3881,plain,(
    ! [A_291,B_292,C_293] :
      ( ~ r1_xboole_0(A_291,B_292)
      | ~ r2_hidden(C_293,k3_xboole_0(A_291,B_292)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3884,plain,(
    ! [C_293] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_293,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3825,c_3881])).

tff(c_5173,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3884])).

tff(c_4397,plain,(
    ! [A_316,B_317] :
      ( r2_hidden('#skF_2'(A_316,B_317),k3_xboole_0(A_316,B_317))
      | r1_xboole_0(A_316,B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5530,plain,(
    ! [A_373,B_374] :
      ( ~ v1_xboole_0(k3_xboole_0(A_373,B_374))
      | r1_xboole_0(A_373,B_374) ) ),
    inference(resolution,[status(thm)],[c_4397,c_4])).

tff(c_5545,plain,
    ( ~ v1_xboole_0('#skF_5')
    | r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3825,c_5530])).

tff(c_5558,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_5173,c_5545])).

tff(c_60,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3075,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_3002,c_60])).

tff(c_3117,plain,(
    ! [A_250,B_251] :
      ( r1_xboole_0(k1_tarski(A_250),B_251)
      | r2_hidden(A_250,B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3120,plain,(
    ! [B_251] :
      ( r1_xboole_0('#skF_4',B_251)
      | r2_hidden('#skF_3',B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3002,c_3117])).

tff(c_4010,plain,(
    ! [B_297,A_298] :
      ( k3_xboole_0(B_297,k1_tarski(A_298)) = k1_tarski(A_298)
      | ~ r2_hidden(A_298,B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4061,plain,(
    ! [B_297] :
      ( k3_xboole_0(B_297,'#skF_4') = k1_tarski('#skF_3')
      | ~ r2_hidden('#skF_3',B_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3002,c_4010])).

tff(c_4331,plain,(
    ! [B_311] :
      ( k3_xboole_0(B_311,'#skF_4') = '#skF_4'
      | ~ r2_hidden('#skF_3',B_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_4061])).

tff(c_4335,plain,(
    ! [B_251] :
      ( k3_xboole_0(B_251,'#skF_4') = '#skF_4'
      | r1_xboole_0('#skF_4',B_251) ) ),
    inference(resolution,[status(thm)],[c_3120,c_4331])).

tff(c_3848,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3825,c_2])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3916,plain,(
    ! [C_12] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_12,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3848,c_12])).

tff(c_5516,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3916])).

tff(c_5523,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4335,c_5516])).

tff(c_5525,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5523,c_3825])).

tff(c_5527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3075,c_5525])).

tff(c_5559,plain,(
    ! [C_375] : ~ r2_hidden(C_375,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3916])).

tff(c_5567,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_5559])).

tff(c_5572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5558,c_5567])).

tff(c_5575,plain,(
    ! [C_376] : ~ r2_hidden(C_376,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3884])).

tff(c_5585,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_5575])).

tff(c_5588,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5585,c_8])).

tff(c_5592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3001,c_5588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:48:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.95  
% 4.82/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.82/1.96  
% 4.82/1.96  %Foreground sorts:
% 4.82/1.96  
% 4.82/1.96  
% 4.82/1.96  %Background operators:
% 4.82/1.96  
% 4.82/1.96  
% 4.82/1.96  %Foreground operators:
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.82/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.82/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.82/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.82/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.82/1.96  tff('#skF_5', type, '#skF_5': $i).
% 4.82/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.82/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.82/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.82/1.96  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.96  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.82/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.82/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.82/1.96  
% 5.12/1.97  tff(f_125, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.12/1.97  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.12/1.97  tff(f_104, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 5.12/1.97  tff(f_81, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.12/1.97  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.12/1.97  tff(f_100, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.12/1.97  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.12/1.97  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.12/1.97  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.12/1.97  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.12/1.97  tff(f_77, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.12/1.97  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.12/1.97  tff(f_79, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.12/1.97  tff(f_75, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.12/1.97  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.12/1.97  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.12/1.97  tff(c_58, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.12/1.97  tff(c_99, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 5.12/1.97  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.12/1.97  tff(c_56, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.12/1.97  tff(c_85, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_56])).
% 5.12/1.97  tff(c_1068, plain, (![B_136, A_137]: (k3_xboole_0(B_136, k1_tarski(A_137))=k1_tarski(A_137) | ~r2_hidden(A_137, B_136))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.12/1.97  tff(c_62, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.12/1.97  tff(c_95, plain, (![A_73, B_74]: (r1_tarski(A_73, k2_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.12/1.97  tff(c_98, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_95])).
% 5.12/1.97  tff(c_199, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.12/1.97  tff(c_213, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_98, c_199])).
% 5.12/1.97  tff(c_1093, plain, (k1_tarski('#skF_3')='#skF_4' | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1068, c_213])).
% 5.12/1.97  tff(c_1129, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_85, c_1093])).
% 5.12/1.97  tff(c_50, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), B_62) | r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.12/1.97  tff(c_714, plain, (![A_115, B_116, C_117]: (~r1_xboole_0(A_115, B_116) | ~r2_hidden(C_117, k3_xboole_0(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.12/1.97  tff(c_723, plain, (![C_117]: (~r1_xboole_0('#skF_4', k1_tarski('#skF_3')) | ~r2_hidden(C_117, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_714])).
% 5.12/1.97  tff(c_744, plain, (~r1_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_723])).
% 5.12/1.97  tff(c_1657, plain, (![A_156, B_157]: (r2_hidden('#skF_2'(A_156, B_157), k3_xboole_0(A_156, B_157)) | r1_xboole_0(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.12/1.97  tff(c_1684, plain, (r2_hidden('#skF_2'('#skF_4', k1_tarski('#skF_3')), '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_1657])).
% 5.12/1.97  tff(c_1693, plain, (r2_hidden('#skF_2'('#skF_4', k1_tarski('#skF_3')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_744, c_1684])).
% 5.12/1.97  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.12/1.97  tff(c_1697, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1693, c_4])).
% 5.12/1.97  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/1.97  tff(c_2284, plain, (![A_183, B_184]: (~r1_xboole_0(A_183, B_184) | v1_xboole_0(k3_xboole_0(A_183, B_184)))), inference(resolution, [status(thm)], [c_6, c_714])).
% 5.12/1.97  tff(c_2524, plain, (![B_202, A_203]: (~r1_xboole_0(B_202, A_203) | v1_xboole_0(k3_xboole_0(A_203, B_202)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2284])).
% 5.12/1.97  tff(c_2557, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_213, c_2524])).
% 5.12/1.97  tff(c_2567, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1697, c_2557])).
% 5.12/1.97  tff(c_2570, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_2567])).
% 5.12/1.97  tff(c_2574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1129, c_2570])).
% 5.12/1.97  tff(c_2577, plain, (![C_204]: (~r2_hidden(C_204, '#skF_4'))), inference(splitRight, [status(thm)], [c_723])).
% 5.12/1.97  tff(c_2582, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2577])).
% 5.12/1.97  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.12/1.97  tff(c_2585, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2582, c_8])).
% 5.12/1.97  tff(c_2589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_2585])).
% 5.12/1.97  tff(c_2590, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 5.12/1.97  tff(c_34, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.12/1.97  tff(c_2591, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 5.12/1.97  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.12/1.97  tff(c_2827, plain, (![A_229, B_230]: (k4_xboole_0(A_229, B_230)='#skF_4' | ~r1_tarski(A_229, B_230))), inference(demodulation, [status(thm), theory('equality')], [c_2591, c_16])).
% 5.12/1.97  tff(c_2915, plain, (![A_235, B_236]: (k4_xboole_0(A_235, k2_xboole_0(A_235, B_236))='#skF_4')), inference(resolution, [status(thm)], [c_34, c_2827])).
% 5.12/1.97  tff(c_30, plain, (![A_28, B_29]: (r1_tarski(k4_xboole_0(A_28, B_29), A_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.12/1.97  tff(c_2925, plain, (![A_235]: (r1_tarski('#skF_4', A_235))), inference(superposition, [status(thm), theory('equality')], [c_2915, c_30])).
% 5.12/1.97  tff(c_2951, plain, (![A_238, B_239]: (k2_xboole_0(A_238, B_239)=B_239 | ~r1_tarski(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.12/1.97  tff(c_2967, plain, (![A_235]: (k2_xboole_0('#skF_4', A_235)=A_235)), inference(resolution, [status(thm)], [c_2925, c_2951])).
% 5.12/1.97  tff(c_2998, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2967, c_62])).
% 5.12/1.97  tff(c_3000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2590, c_2998])).
% 5.12/1.97  tff(c_3001, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_56])).
% 5.12/1.97  tff(c_32, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=A_30)), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.12/1.97  tff(c_28, plain, (![A_27]: (k3_xboole_0(A_27, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.12/1.97  tff(c_3463, plain, (![A_273, B_274]: (k5_xboole_0(A_273, k3_xboole_0(A_273, B_274))=k4_xboole_0(A_273, B_274))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.12/1.97  tff(c_3493, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=k4_xboole_0(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3463])).
% 5.12/1.97  tff(c_3500, plain, (![A_275]: (k4_xboole_0(A_275, k1_xboole_0)=A_275)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3493])).
% 5.12/1.97  tff(c_3509, plain, (![A_275]: (r1_tarski(A_275, A_275))), inference(superposition, [status(thm), theory('equality')], [c_3500, c_30])).
% 5.12/1.97  tff(c_3002, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_56])).
% 5.12/1.97  tff(c_3004, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_62])).
% 5.12/1.97  tff(c_3765, plain, (![A_287, C_288, B_289]: (r1_tarski(A_287, k2_xboole_0(C_288, B_289)) | ~r1_tarski(A_287, B_289))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.12/1.97  tff(c_3793, plain, (![A_290]: (r1_tarski(A_290, '#skF_4') | ~r1_tarski(A_290, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3004, c_3765])).
% 5.12/1.97  tff(c_3812, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3509, c_3793])).
% 5.12/1.97  tff(c_26, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.12/1.97  tff(c_3825, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_3812, c_26])).
% 5.12/1.97  tff(c_3881, plain, (![A_291, B_292, C_293]: (~r1_xboole_0(A_291, B_292) | ~r2_hidden(C_293, k3_xboole_0(A_291, B_292)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.12/1.97  tff(c_3884, plain, (![C_293]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_293, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3825, c_3881])).
% 5.12/1.97  tff(c_5173, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_3884])).
% 5.12/1.97  tff(c_4397, plain, (![A_316, B_317]: (r2_hidden('#skF_2'(A_316, B_317), k3_xboole_0(A_316, B_317)) | r1_xboole_0(A_316, B_317))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.12/1.97  tff(c_5530, plain, (![A_373, B_374]: (~v1_xboole_0(k3_xboole_0(A_373, B_374)) | r1_xboole_0(A_373, B_374))), inference(resolution, [status(thm)], [c_4397, c_4])).
% 5.12/1.97  tff(c_5545, plain, (~v1_xboole_0('#skF_5') | r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3825, c_5530])).
% 5.12/1.97  tff(c_5558, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_5173, c_5545])).
% 5.12/1.97  tff(c_60, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.12/1.97  tff(c_3075, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_3002, c_60])).
% 5.12/1.97  tff(c_3117, plain, (![A_250, B_251]: (r1_xboole_0(k1_tarski(A_250), B_251) | r2_hidden(A_250, B_251))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.12/1.97  tff(c_3120, plain, (![B_251]: (r1_xboole_0('#skF_4', B_251) | r2_hidden('#skF_3', B_251))), inference(superposition, [status(thm), theory('equality')], [c_3002, c_3117])).
% 5.12/1.97  tff(c_4010, plain, (![B_297, A_298]: (k3_xboole_0(B_297, k1_tarski(A_298))=k1_tarski(A_298) | ~r2_hidden(A_298, B_297))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.12/1.97  tff(c_4061, plain, (![B_297]: (k3_xboole_0(B_297, '#skF_4')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', B_297))), inference(superposition, [status(thm), theory('equality')], [c_3002, c_4010])).
% 5.12/1.97  tff(c_4331, plain, (![B_311]: (k3_xboole_0(B_311, '#skF_4')='#skF_4' | ~r2_hidden('#skF_3', B_311))), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_4061])).
% 5.12/1.97  tff(c_4335, plain, (![B_251]: (k3_xboole_0(B_251, '#skF_4')='#skF_4' | r1_xboole_0('#skF_4', B_251))), inference(resolution, [status(thm)], [c_3120, c_4331])).
% 5.12/1.97  tff(c_3848, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3825, c_2])).
% 5.12/1.97  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.12/1.97  tff(c_3916, plain, (![C_12]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_12, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3848, c_12])).
% 5.12/1.97  tff(c_5516, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3916])).
% 5.12/1.97  tff(c_5523, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_4335, c_5516])).
% 5.12/1.97  tff(c_5525, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5523, c_3825])).
% 5.12/1.97  tff(c_5527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3075, c_5525])).
% 5.12/1.97  tff(c_5559, plain, (![C_375]: (~r2_hidden(C_375, '#skF_5'))), inference(splitRight, [status(thm)], [c_3916])).
% 5.12/1.97  tff(c_5567, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_5559])).
% 5.12/1.97  tff(c_5572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5558, c_5567])).
% 5.12/1.97  tff(c_5575, plain, (![C_376]: (~r2_hidden(C_376, '#skF_5'))), inference(splitRight, [status(thm)], [c_3884])).
% 5.12/1.97  tff(c_5585, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_5575])).
% 5.12/1.97  tff(c_5588, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_5585, c_8])).
% 5.12/1.97  tff(c_5592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3001, c_5588])).
% 5.12/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.97  
% 5.12/1.97  Inference rules
% 5.12/1.97  ----------------------
% 5.12/1.97  #Ref     : 2
% 5.12/1.97  #Sup     : 1375
% 5.12/1.97  #Fact    : 0
% 5.12/1.97  #Define  : 0
% 5.12/1.97  #Split   : 8
% 5.12/1.97  #Chain   : 0
% 5.12/1.97  #Close   : 0
% 5.12/1.97  
% 5.12/1.97  Ordering : KBO
% 5.12/1.97  
% 5.12/1.97  Simplification rules
% 5.12/1.97  ----------------------
% 5.12/1.97  #Subsume      : 123
% 5.12/1.97  #Demod        : 480
% 5.12/1.97  #Tautology    : 917
% 5.12/1.97  #SimpNegUnit  : 23
% 5.12/1.97  #BackRed      : 17
% 5.12/1.97  
% 5.12/1.97  #Partial instantiations: 0
% 5.12/1.97  #Strategies tried      : 1
% 5.12/1.97  
% 5.12/1.97  Timing (in seconds)
% 5.12/1.97  ----------------------
% 5.12/1.98  Preprocessing        : 0.33
% 5.12/1.98  Parsing              : 0.17
% 5.12/1.98  CNF conversion       : 0.02
% 5.12/1.98  Main loop            : 0.83
% 5.12/1.98  Inferencing          : 0.29
% 5.12/1.98  Reduction            : 0.31
% 5.12/1.98  Demodulation         : 0.23
% 5.12/1.98  BG Simplification    : 0.03
% 5.12/1.98  Subsumption          : 0.12
% 5.12/1.98  Abstraction          : 0.03
% 5.12/1.98  MUC search           : 0.00
% 5.12/1.98  Cooper               : 0.00
% 5.12/1.98  Total                : 1.19
% 5.12/1.98  Index Insertion      : 0.00
% 5.12/1.98  Index Deletion       : 0.00
% 5.12/1.98  Index Matching       : 0.00
% 5.12/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
