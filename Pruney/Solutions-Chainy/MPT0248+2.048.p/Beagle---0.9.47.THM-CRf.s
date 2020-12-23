%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:10 EST 2020

% Result     : Theorem 6.03s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 323 expanded)
%              Number of leaves         :   41 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :  149 ( 608 expanded)
%              Number of equality atoms :   90 ( 429 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_76,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_62,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_109,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_94,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_110,plain,(
    ! [A_72,B_73] : r1_tarski(A_72,k2_xboole_0(A_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_113,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_110])).

tff(c_1725,plain,(
    ! [B_163,A_164] :
      ( k1_tarski(B_163) = A_164
      | k1_xboole_0 = A_164
      | ~ r1_tarski(A_164,k1_tarski(B_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1748,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_113,c_1725])).

tff(c_1760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_94,c_1748])).

tff(c_1762,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_56,plain,(
    ! [B_64] : r1_tarski(k1_xboole_0,k1_tarski(B_64)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1765,plain,(
    ! [B_64] : r1_tarski('#skF_4',k1_tarski(B_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_56])).

tff(c_1972,plain,(
    ! [A_182,B_183] :
      ( k3_xboole_0(A_182,B_183) = A_182
      | ~ r1_tarski(A_182,B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1995,plain,(
    ! [B_64] : k3_xboole_0('#skF_4',k1_tarski(B_64)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1765,c_1972])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2035,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_14])).

tff(c_1761,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2783,plain,(
    ! [A_238,B_239] :
      ( r2_hidden('#skF_1'(A_238,B_239),A_238)
      | r1_tarski(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2380,plain,(
    ! [A_212,B_213,C_214] :
      ( ~ r1_xboole_0(A_212,B_213)
      | ~ r2_hidden(C_214,k3_xboole_0(A_212,B_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2395,plain,(
    ! [B_64,C_214] :
      ( ~ r1_xboole_0('#skF_4',k1_tarski(B_64))
      | ~ r2_hidden(C_214,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1995,c_2380])).

tff(c_2684,plain,(
    ! [C_214] : ~ r2_hidden(C_214,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2395])).

tff(c_2811,plain,(
    ! [B_241] : r1_tarski('#skF_4',B_241) ),
    inference(resolution,[status(thm)],[c_2783,c_2684])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2818,plain,(
    ! [B_241] : k2_xboole_0('#skF_4',B_241) = B_241 ),
    inference(resolution,[status(thm)],[c_2811,c_24])).

tff(c_3072,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_66])).

tff(c_3074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1761,c_3072])).

tff(c_3119,plain,(
    ! [B_250] : ~ r1_xboole_0('#skF_4',k1_tarski(B_250)) ),
    inference(splitRight,[status(thm)],[c_2395])).

tff(c_3122,plain,(
    ! [B_250] : k3_xboole_0('#skF_4',k1_tarski(B_250)) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_2035,c_3119])).

tff(c_3126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_3122])).

tff(c_3127,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3128,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3165,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3128,c_3128,c_64])).

tff(c_3135,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3128,c_66])).

tff(c_30,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3131,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_56])).

tff(c_3394,plain,(
    ! [A_273,B_274] :
      ( k3_xboole_0(A_273,B_274) = A_273
      | ~ r1_tarski(A_273,B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3433,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3131,c_3394])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3457,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3433,c_2])).

tff(c_4144,plain,(
    ! [A_304,B_305,C_306] :
      ( ~ r1_xboole_0(A_304,B_305)
      | ~ r2_hidden(C_306,k3_xboole_0(A_304,B_305)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4169,plain,(
    ! [C_306] :
      ( ~ r1_xboole_0(k1_xboole_0,'#skF_4')
      | ~ r2_hidden(C_306,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3433,c_4144])).

tff(c_4327,plain,(
    ~ r1_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4169])).

tff(c_4381,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_4327])).

tff(c_4385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3457,c_2,c_4381])).

tff(c_4388,plain,(
    ! [C_316] : ~ r2_hidden(C_316,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4169])).

tff(c_4403,plain,(
    ! [B_317] : r1_tarski(k1_xboole_0,B_317) ),
    inference(resolution,[status(thm)],[c_10,c_4388])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4450,plain,(
    ! [B_319] : k3_xboole_0(k1_xboole_0,B_319) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4403,c_26])).

tff(c_4484,plain,(
    ! [B_319] : k3_xboole_0(B_319,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4450,c_2])).

tff(c_4591,plain,(
    ! [A_321,B_322] : k5_xboole_0(A_321,k3_xboole_0(A_321,B_322)) = k4_xboole_0(A_321,B_322) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4604,plain,(
    ! [B_319] : k5_xboole_0(B_319,k1_xboole_0) = k4_xboole_0(B_319,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4484,c_4591])).

tff(c_4630,plain,(
    ! [B_319] : k4_xboole_0(B_319,k1_xboole_0) = B_319 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4604])).

tff(c_3985,plain,(
    ! [A_297,B_298] :
      ( ~ r2_hidden('#skF_1'(A_297,B_298),B_298)
      | r1_tarski(A_297,B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3993,plain,(
    ! [A_299] : r1_tarski(A_299,A_299) ),
    inference(resolution,[status(thm)],[c_10,c_3985])).

tff(c_4005,plain,(
    ! [A_300] : k2_xboole_0(A_300,A_300) = A_300 ),
    inference(resolution,[status(thm)],[c_3993,c_24])).

tff(c_28,plain,(
    ! [A_25,B_26,C_27] : r1_tarski(k3_xboole_0(A_25,B_26),k2_xboole_0(A_25,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4022,plain,(
    ! [A_300,B_26] : r1_tarski(k3_xboole_0(A_300,B_26),A_300) ),
    inference(superposition,[status(thm),theory(equality)],[c_4005,c_28])).

tff(c_4904,plain,(
    ! [B_342,A_343] :
      ( k1_tarski(B_342) = A_343
      | k1_xboole_0 = A_343
      | ~ r1_tarski(A_343,k1_tarski(B_342)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4923,plain,(
    ! [A_343] :
      ( k1_tarski('#skF_3') = A_343
      | k1_xboole_0 = A_343
      | ~ r1_tarski(A_343,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_4904])).

tff(c_4932,plain,(
    ! [A_344] :
      ( A_344 = '#skF_4'
      | k1_xboole_0 = A_344
      | ~ r1_tarski(A_344,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3128,c_4923])).

tff(c_7768,plain,(
    ! [B_450] :
      ( k3_xboole_0('#skF_4',B_450) = '#skF_4'
      | k3_xboole_0('#skF_4',B_450) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4022,c_4932])).

tff(c_5515,plain,(
    ! [A_362,B_363] : k4_xboole_0(k2_xboole_0(A_362,B_363),k3_xboole_0(A_362,B_363)) = k5_xboole_0(A_362,B_363) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5560,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3135,c_5515])).

tff(c_7827,plain,
    ( k5_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7768,c_5560])).

tff(c_7932,plain,
    ( k5_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_7827])).

tff(c_8396,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7932])).

tff(c_4179,plain,(
    ! [A_307,B_308] : r1_tarski(k3_xboole_0(A_307,B_308),A_307) ),
    inference(superposition,[status(thm),theory(equality)],[c_4005,c_28])).

tff(c_4248,plain,(
    ! [A_310,B_311] : r1_tarski(k3_xboole_0(A_310,B_311),B_311) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4179])).

tff(c_4282,plain,(
    ! [A_310,B_311] : k2_xboole_0(k3_xboole_0(A_310,B_311),B_311) = B_311 ),
    inference(resolution,[status(thm)],[c_4248,c_24])).

tff(c_8459,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_8396,c_4282])).

tff(c_8501,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_8459])).

tff(c_8503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3165,c_8501])).

tff(c_8504,plain,(
    k5_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7932])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3199,plain,(
    ! [B_257,A_258] : k5_xboole_0(B_257,A_258) = k5_xboole_0(A_258,B_257) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3215,plain,(
    ! [A_258] : k5_xboole_0(k1_xboole_0,A_258) = A_258 ),
    inference(superposition,[status(thm),theory(equality)],[c_3199,c_30])).

tff(c_36,plain,(
    ! [A_34] : k5_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5761,plain,(
    ! [A_368,B_369,C_370] : k5_xboole_0(k5_xboole_0(A_368,B_369),C_370) = k5_xboole_0(A_368,k5_xboole_0(B_369,C_370)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5825,plain,(
    ! [A_34,C_370] : k5_xboole_0(A_34,k5_xboole_0(A_34,C_370)) = k5_xboole_0(k1_xboole_0,C_370) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5761])).

tff(c_5839,plain,(
    ! [A_371,C_372] : k5_xboole_0(A_371,k5_xboole_0(A_371,C_372)) = C_372 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3215,c_5825])).

tff(c_5904,plain,(
    ! [A_373,B_374] : k5_xboole_0(A_373,k5_xboole_0(B_374,A_373)) = B_374 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5839])).

tff(c_5882,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5839])).

tff(c_5907,plain,(
    ! [B_374,A_373] : k5_xboole_0(k5_xboole_0(B_374,A_373),B_374) = A_373 ),
    inference(superposition,[status(thm),theory(equality)],[c_5904,c_5882])).

tff(c_8513,plain,(
    k5_xboole_0('#skF_4','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_8504,c_5907])).

tff(c_8555,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_8513,c_36])).

tff(c_8564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3127,c_8555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.03/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.28  
% 6.03/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.03/2.28  
% 6.03/2.28  %Foreground sorts:
% 6.03/2.28  
% 6.03/2.28  
% 6.03/2.28  %Background operators:
% 6.03/2.28  
% 6.03/2.28  
% 6.03/2.28  %Foreground operators:
% 6.03/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.03/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.03/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.03/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.03/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.03/2.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.03/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.03/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.03/2.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.03/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.03/2.28  tff('#skF_5', type, '#skF_5': $i).
% 6.03/2.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.03/2.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.03/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.03/2.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.03/2.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.03/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.03/2.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.03/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.03/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.03/2.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.03/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.03/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.03/2.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.03/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.03/2.28  
% 6.31/2.30  tff(f_117, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.31/2.30  tff(f_72, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.31/2.30  tff(f_96, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.31/2.30  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.31/2.30  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.31/2.30  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.31/2.30  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.31/2.30  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.31/2.30  tff(f_70, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.31/2.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.31/2.30  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.31/2.30  tff(f_68, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 6.31/2.30  tff(f_56, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 6.31/2.30  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.31/2.30  tff(f_76, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.31/2.30  tff(f_74, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.31/2.30  tff(c_62, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.31/2.30  tff(c_109, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 6.31/2.30  tff(c_60, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.31/2.30  tff(c_94, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 6.31/2.30  tff(c_66, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.31/2.30  tff(c_110, plain, (![A_72, B_73]: (r1_tarski(A_72, k2_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.31/2.30  tff(c_113, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_110])).
% 6.31/2.30  tff(c_1725, plain, (![B_163, A_164]: (k1_tarski(B_163)=A_164 | k1_xboole_0=A_164 | ~r1_tarski(A_164, k1_tarski(B_163)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.31/2.30  tff(c_1748, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_113, c_1725])).
% 6.31/2.30  tff(c_1760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_94, c_1748])).
% 6.31/2.30  tff(c_1762, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 6.31/2.30  tff(c_56, plain, (![B_64]: (r1_tarski(k1_xboole_0, k1_tarski(B_64)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.31/2.30  tff(c_1765, plain, (![B_64]: (r1_tarski('#skF_4', k1_tarski(B_64)))), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_56])).
% 6.31/2.30  tff(c_1972, plain, (![A_182, B_183]: (k3_xboole_0(A_182, B_183)=A_182 | ~r1_tarski(A_182, B_183))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.31/2.30  tff(c_1995, plain, (![B_64]: (k3_xboole_0('#skF_4', k1_tarski(B_64))='#skF_4')), inference(resolution, [status(thm)], [c_1765, c_1972])).
% 6.31/2.30  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.31/2.30  tff(c_2035, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_14])).
% 6.31/2.30  tff(c_1761, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 6.31/2.30  tff(c_2783, plain, (![A_238, B_239]: (r2_hidden('#skF_1'(A_238, B_239), A_238) | r1_tarski(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.31/2.30  tff(c_2380, plain, (![A_212, B_213, C_214]: (~r1_xboole_0(A_212, B_213) | ~r2_hidden(C_214, k3_xboole_0(A_212, B_213)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.31/2.30  tff(c_2395, plain, (![B_64, C_214]: (~r1_xboole_0('#skF_4', k1_tarski(B_64)) | ~r2_hidden(C_214, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1995, c_2380])).
% 6.31/2.30  tff(c_2684, plain, (![C_214]: (~r2_hidden(C_214, '#skF_4'))), inference(splitLeft, [status(thm)], [c_2395])).
% 6.31/2.30  tff(c_2811, plain, (![B_241]: (r1_tarski('#skF_4', B_241))), inference(resolution, [status(thm)], [c_2783, c_2684])).
% 6.31/2.30  tff(c_24, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.31/2.30  tff(c_2818, plain, (![B_241]: (k2_xboole_0('#skF_4', B_241)=B_241)), inference(resolution, [status(thm)], [c_2811, c_24])).
% 6.31/2.30  tff(c_3072, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2818, c_66])).
% 6.31/2.30  tff(c_3074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1761, c_3072])).
% 6.31/2.30  tff(c_3119, plain, (![B_250]: (~r1_xboole_0('#skF_4', k1_tarski(B_250)))), inference(splitRight, [status(thm)], [c_2395])).
% 6.31/2.30  tff(c_3122, plain, (![B_250]: (k3_xboole_0('#skF_4', k1_tarski(B_250))!='#skF_4')), inference(resolution, [status(thm)], [c_2035, c_3119])).
% 6.31/2.30  tff(c_3126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1995, c_3122])).
% 6.31/2.30  tff(c_3127, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 6.31/2.30  tff(c_3128, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 6.31/2.30  tff(c_64, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.31/2.30  tff(c_3165, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3128, c_3128, c_64])).
% 6.31/2.30  tff(c_3135, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3128, c_66])).
% 6.31/2.30  tff(c_30, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.31/2.30  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.31/2.30  tff(c_3131, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3128, c_56])).
% 6.31/2.30  tff(c_3394, plain, (![A_273, B_274]: (k3_xboole_0(A_273, B_274)=A_273 | ~r1_tarski(A_273, B_274))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.31/2.30  tff(c_3433, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3131, c_3394])).
% 6.31/2.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.31/2.30  tff(c_3457, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3433, c_2])).
% 6.31/2.30  tff(c_4144, plain, (![A_304, B_305, C_306]: (~r1_xboole_0(A_304, B_305) | ~r2_hidden(C_306, k3_xboole_0(A_304, B_305)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.31/2.30  tff(c_4169, plain, (![C_306]: (~r1_xboole_0(k1_xboole_0, '#skF_4') | ~r2_hidden(C_306, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3433, c_4144])).
% 6.31/2.30  tff(c_4327, plain, (~r1_xboole_0(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_4169])).
% 6.31/2.30  tff(c_4381, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_4327])).
% 6.31/2.30  tff(c_4385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3457, c_2, c_4381])).
% 6.31/2.30  tff(c_4388, plain, (![C_316]: (~r2_hidden(C_316, k1_xboole_0))), inference(splitRight, [status(thm)], [c_4169])).
% 6.31/2.30  tff(c_4403, plain, (![B_317]: (r1_tarski(k1_xboole_0, B_317))), inference(resolution, [status(thm)], [c_10, c_4388])).
% 6.31/2.30  tff(c_26, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.31/2.30  tff(c_4450, plain, (![B_319]: (k3_xboole_0(k1_xboole_0, B_319)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4403, c_26])).
% 6.31/2.30  tff(c_4484, plain, (![B_319]: (k3_xboole_0(B_319, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4450, c_2])).
% 6.31/2.30  tff(c_4591, plain, (![A_321, B_322]: (k5_xboole_0(A_321, k3_xboole_0(A_321, B_322))=k4_xboole_0(A_321, B_322))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.31/2.30  tff(c_4604, plain, (![B_319]: (k5_xboole_0(B_319, k1_xboole_0)=k4_xboole_0(B_319, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4484, c_4591])).
% 6.31/2.30  tff(c_4630, plain, (![B_319]: (k4_xboole_0(B_319, k1_xboole_0)=B_319)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4604])).
% 6.31/2.30  tff(c_3985, plain, (![A_297, B_298]: (~r2_hidden('#skF_1'(A_297, B_298), B_298) | r1_tarski(A_297, B_298))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.31/2.30  tff(c_3993, plain, (![A_299]: (r1_tarski(A_299, A_299))), inference(resolution, [status(thm)], [c_10, c_3985])).
% 6.31/2.30  tff(c_4005, plain, (![A_300]: (k2_xboole_0(A_300, A_300)=A_300)), inference(resolution, [status(thm)], [c_3993, c_24])).
% 6.31/2.30  tff(c_28, plain, (![A_25, B_26, C_27]: (r1_tarski(k3_xboole_0(A_25, B_26), k2_xboole_0(A_25, C_27)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.31/2.30  tff(c_4022, plain, (![A_300, B_26]: (r1_tarski(k3_xboole_0(A_300, B_26), A_300))), inference(superposition, [status(thm), theory('equality')], [c_4005, c_28])).
% 6.31/2.30  tff(c_4904, plain, (![B_342, A_343]: (k1_tarski(B_342)=A_343 | k1_xboole_0=A_343 | ~r1_tarski(A_343, k1_tarski(B_342)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.31/2.30  tff(c_4923, plain, (![A_343]: (k1_tarski('#skF_3')=A_343 | k1_xboole_0=A_343 | ~r1_tarski(A_343, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3128, c_4904])).
% 6.31/2.30  tff(c_4932, plain, (![A_344]: (A_344='#skF_4' | k1_xboole_0=A_344 | ~r1_tarski(A_344, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3128, c_4923])).
% 6.31/2.30  tff(c_7768, plain, (![B_450]: (k3_xboole_0('#skF_4', B_450)='#skF_4' | k3_xboole_0('#skF_4', B_450)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4022, c_4932])).
% 6.31/2.30  tff(c_5515, plain, (![A_362, B_363]: (k4_xboole_0(k2_xboole_0(A_362, B_363), k3_xboole_0(A_362, B_363))=k5_xboole_0(A_362, B_363))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.31/2.30  tff(c_5560, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3135, c_5515])).
% 6.31/2.30  tff(c_7827, plain, (k5_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7768, c_5560])).
% 6.31/2.30  tff(c_7932, plain, (k5_xboole_0('#skF_4', '#skF_5')='#skF_4' | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_7827])).
% 6.31/2.30  tff(c_8396, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_7932])).
% 6.31/2.30  tff(c_4179, plain, (![A_307, B_308]: (r1_tarski(k3_xboole_0(A_307, B_308), A_307))), inference(superposition, [status(thm), theory('equality')], [c_4005, c_28])).
% 6.31/2.30  tff(c_4248, plain, (![A_310, B_311]: (r1_tarski(k3_xboole_0(A_310, B_311), B_311))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4179])).
% 6.31/2.30  tff(c_4282, plain, (![A_310, B_311]: (k2_xboole_0(k3_xboole_0(A_310, B_311), B_311)=B_311)), inference(resolution, [status(thm)], [c_4248, c_24])).
% 6.31/2.30  tff(c_8459, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_8396, c_4282])).
% 6.31/2.30  tff(c_8501, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_8459])).
% 6.31/2.30  tff(c_8503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3165, c_8501])).
% 6.31/2.30  tff(c_8504, plain, (k5_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_7932])).
% 6.31/2.30  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.31/2.30  tff(c_3199, plain, (![B_257, A_258]: (k5_xboole_0(B_257, A_258)=k5_xboole_0(A_258, B_257))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.31/2.30  tff(c_3215, plain, (![A_258]: (k5_xboole_0(k1_xboole_0, A_258)=A_258)), inference(superposition, [status(thm), theory('equality')], [c_3199, c_30])).
% 6.31/2.30  tff(c_36, plain, (![A_34]: (k5_xboole_0(A_34, A_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.31/2.30  tff(c_5761, plain, (![A_368, B_369, C_370]: (k5_xboole_0(k5_xboole_0(A_368, B_369), C_370)=k5_xboole_0(A_368, k5_xboole_0(B_369, C_370)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.31/2.30  tff(c_5825, plain, (![A_34, C_370]: (k5_xboole_0(A_34, k5_xboole_0(A_34, C_370))=k5_xboole_0(k1_xboole_0, C_370))), inference(superposition, [status(thm), theory('equality')], [c_36, c_5761])).
% 6.31/2.30  tff(c_5839, plain, (![A_371, C_372]: (k5_xboole_0(A_371, k5_xboole_0(A_371, C_372))=C_372)), inference(demodulation, [status(thm), theory('equality')], [c_3215, c_5825])).
% 6.31/2.30  tff(c_5904, plain, (![A_373, B_374]: (k5_xboole_0(A_373, k5_xboole_0(B_374, A_373))=B_374)), inference(superposition, [status(thm), theory('equality')], [c_4, c_5839])).
% 6.31/2.30  tff(c_5882, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_5839])).
% 6.31/2.30  tff(c_5907, plain, (![B_374, A_373]: (k5_xboole_0(k5_xboole_0(B_374, A_373), B_374)=A_373)), inference(superposition, [status(thm), theory('equality')], [c_5904, c_5882])).
% 6.31/2.30  tff(c_8513, plain, (k5_xboole_0('#skF_4', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_8504, c_5907])).
% 6.31/2.30  tff(c_8555, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_8513, c_36])).
% 6.31/2.30  tff(c_8564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3127, c_8555])).
% 6.31/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.30  
% 6.31/2.30  Inference rules
% 6.31/2.30  ----------------------
% 6.31/2.30  #Ref     : 1
% 6.31/2.30  #Sup     : 2051
% 6.31/2.30  #Fact    : 2
% 6.31/2.30  #Define  : 0
% 6.31/2.30  #Split   : 8
% 6.31/2.30  #Chain   : 0
% 6.31/2.30  #Close   : 0
% 6.31/2.30  
% 6.31/2.30  Ordering : KBO
% 6.31/2.30  
% 6.31/2.30  Simplification rules
% 6.31/2.30  ----------------------
% 6.31/2.30  #Subsume      : 170
% 6.31/2.30  #Demod        : 1180
% 6.31/2.30  #Tautology    : 1362
% 6.31/2.30  #SimpNegUnit  : 27
% 6.31/2.30  #BackRed      : 41
% 6.31/2.30  
% 6.31/2.30  #Partial instantiations: 0
% 6.31/2.30  #Strategies tried      : 1
% 6.31/2.30  
% 6.31/2.30  Timing (in seconds)
% 6.31/2.30  ----------------------
% 6.31/2.30  Preprocessing        : 0.35
% 6.31/2.30  Parsing              : 0.19
% 6.31/2.30  CNF conversion       : 0.02
% 6.31/2.30  Main loop            : 1.15
% 6.31/2.30  Inferencing          : 0.39
% 6.31/2.30  Reduction            : 0.46
% 6.31/2.30  Demodulation         : 0.36
% 6.31/2.30  BG Simplification    : 0.04
% 6.31/2.30  Subsumption          : 0.17
% 6.31/2.30  Abstraction          : 0.05
% 6.31/2.30  MUC search           : 0.00
% 6.31/2.30  Cooper               : 0.00
% 6.31/2.30  Total                : 1.55
% 6.31/2.30  Index Insertion      : 0.00
% 6.31/2.30  Index Deletion       : 0.00
% 6.31/2.30  Index Matching       : 0.00
% 6.31/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
