%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:14 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 325 expanded)
%              Number of leaves         :   39 ( 118 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 ( 585 expanded)
%              Number of equality atoms :   99 ( 479 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_78,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_70,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_132,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_68,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_133,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_143,plain,(
    ! [A_80,B_81] : r1_tarski(A_80,k2_xboole_0(A_80,B_81)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_146,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_143])).

tff(c_594,plain,(
    ! [B_131,A_132] :
      ( k1_tarski(B_131) = A_132
      | k1_xboole_0 = A_132
      | ~ r1_tarski(A_132,k1_tarski(B_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_612,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_146,c_594])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_133,c_612])).

tff(c_632,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_633,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_664,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_633,c_72])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_665,plain,(
    ! [B_136,A_137] : k5_xboole_0(B_136,A_137) = k5_xboole_0(A_137,B_136) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_681,plain,(
    ! [A_137] : k5_xboole_0(k1_xboole_0,A_137) = A_137 ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_28])).

tff(c_36,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1856,plain,(
    ! [A_228,B_229,C_230] : k5_xboole_0(k5_xboole_0(A_228,B_229),C_230) = k5_xboole_0(A_228,k5_xboole_0(B_229,C_230)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1909,plain,(
    ! [A_32,C_230] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_230)) = k5_xboole_0(k1_xboole_0,C_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1856])).

tff(c_1923,plain,(
    ! [A_231,C_232] : k5_xboole_0(A_231,k5_xboole_0(A_231,C_232)) = C_232 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_1909])).

tff(c_1963,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1923])).

tff(c_1985,plain,(
    ! [A_233,B_234] : k5_xboole_0(A_233,k5_xboole_0(B_234,A_233)) = B_234 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1923])).

tff(c_2012,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),B_2) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_1985])).

tff(c_634,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_74])).

tff(c_2293,plain,(
    ! [A_241,B_242] : k5_xboole_0(k5_xboole_0(A_241,B_242),k2_xboole_0(A_241,B_242)) = k3_xboole_0(A_241,B_242) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2378,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_2293])).

tff(c_2395,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_2378])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(k3_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1180,plain,(
    ! [B_182,A_183] :
      ( k1_tarski(B_182) = A_183
      | k1_xboole_0 = A_183
      | ~ r1_tarski(A_183,k1_tarski(B_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1187,plain,(
    ! [A_183] :
      ( k1_tarski('#skF_3') = A_183
      | k1_xboole_0 = A_183
      | ~ r1_tarski(A_183,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_1180])).

tff(c_1206,plain,(
    ! [A_184] :
      ( A_184 = '#skF_4'
      | k1_xboole_0 = A_184
      | ~ r1_tarski(A_184,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_1187])).

tff(c_1227,plain,(
    ! [B_22] :
      ( k3_xboole_0('#skF_4',B_22) = '#skF_4'
      | k3_xboole_0('#skF_4',B_22) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_1206])).

tff(c_2404,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2395,c_1227])).

tff(c_2428,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2404])).

tff(c_2430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_664,c_2428])).

tff(c_2431,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2487,plain,(
    ! [B_249,A_250] : k5_xboole_0(B_249,A_250) = k5_xboole_0(A_250,B_249) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2432,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2433,plain,(
    ! [A_23] : k5_xboole_0(A_23,'#skF_4') = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_28])).

tff(c_2503,plain,(
    ! [A_250] : k5_xboole_0('#skF_4',A_250) = A_250 ),
    inference(superposition,[status(thm),theory(equality)],[c_2487,c_2433])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3063,plain,(
    ! [A_313,B_314] :
      ( r2_hidden('#skF_2'(A_313,B_314),k3_xboole_0(A_313,B_314))
      | r1_xboole_0(A_313,B_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3080,plain,(
    ! [A_317] :
      ( r2_hidden('#skF_2'(A_317,A_317),A_317)
      | r1_xboole_0(A_317,A_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3063])).

tff(c_56,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k1_tarski(A_63),B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    ! [B_68] : r1_tarski(k1_xboole_0,k1_tarski(B_68)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2434,plain,(
    ! [B_68] : r1_tarski('#skF_4',k1_tarski(B_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_64])).

tff(c_2714,plain,(
    ! [B_280,A_281] :
      ( B_280 = A_281
      | ~ r1_tarski(B_280,A_281)
      | ~ r1_tarski(A_281,B_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2733,plain,(
    ! [B_282] :
      ( k1_tarski(B_282) = '#skF_4'
      | ~ r1_tarski(k1_tarski(B_282),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2434,c_2714])).

tff(c_2738,plain,(
    ! [A_63] :
      ( k1_tarski(A_63) = '#skF_4'
      | ~ r2_hidden(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_2733])).

tff(c_3092,plain,
    ( k1_tarski('#skF_2'('#skF_4','#skF_4')) = '#skF_4'
    | r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3080,c_2738])).

tff(c_3094,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3092])).

tff(c_2701,plain,(
    ! [A_276,B_277] :
      ( r2_hidden('#skF_1'(A_276,B_277),A_276)
      | r1_tarski(A_276,B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2810,plain,(
    ! [A_288,B_289,B_290] :
      ( ~ r1_xboole_0(A_288,B_289)
      | r1_tarski(k3_xboole_0(A_288,B_289),B_290) ) ),
    inference(resolution,[status(thm)],[c_2701,c_16])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3012,plain,(
    ! [A_310,B_311,B_312] :
      ( k2_xboole_0(k3_xboole_0(A_310,B_311),B_312) = B_312
      | ~ r1_xboole_0(A_310,B_311) ) ),
    inference(resolution,[status(thm)],[c_2810,c_24])).

tff(c_3053,plain,(
    ! [A_10,B_312] :
      ( k2_xboole_0(A_10,B_312) = B_312
      | ~ r1_xboole_0(A_10,A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3012])).

tff(c_3173,plain,(
    ! [B_312] : k2_xboole_0('#skF_4',B_312) = B_312 ),
    inference(resolution,[status(thm)],[c_3094,c_3053])).

tff(c_3213,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3173,c_74])).

tff(c_3215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2431,c_3213])).

tff(c_3216,plain,(
    k1_tarski('#skF_2'('#skF_4','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3092])).

tff(c_60,plain,(
    ! [B_68,A_67] :
      ( k1_tarski(B_68) = A_67
      | k1_xboole_0 = A_67
      | ~ r1_tarski(A_67,k1_tarski(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2739,plain,(
    ! [B_68,A_67] :
      ( k1_tarski(B_68) = A_67
      | A_67 = '#skF_4'
      | ~ r1_tarski(A_67,k1_tarski(B_68)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_60])).

tff(c_3331,plain,(
    ! [A_67] :
      ( k1_tarski('#skF_2'('#skF_4','#skF_4')) = A_67
      | A_67 = '#skF_4'
      | ~ r1_tarski(A_67,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3216,c_2739])).

tff(c_4054,plain,(
    ! [A_346] :
      ( A_346 = '#skF_4'
      | A_346 = '#skF_4'
      | ~ r1_tarski(A_346,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3216,c_3331])).

tff(c_4073,plain,(
    ! [B_22] : k3_xboole_0('#skF_4',B_22) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_4054])).

tff(c_3218,plain,(
    ! [A_322,B_323] : k5_xboole_0(k5_xboole_0(A_322,B_323),k2_xboole_0(A_322,B_323)) = k3_xboole_0(A_322,B_323) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3275,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_3218])).

tff(c_3286,plain,(
    k5_xboole_0('#skF_5',k1_tarski('#skF_3')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_3275])).

tff(c_2435,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_36])).

tff(c_3396,plain,(
    ! [A_326,B_327,C_328] : k5_xboole_0(k5_xboole_0(A_326,B_327),C_328) = k5_xboole_0(A_326,k5_xboole_0(B_327,C_328)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3458,plain,(
    ! [A_32,C_328] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_328)) = k5_xboole_0('#skF_4',C_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_2435,c_3396])).

tff(c_3479,plain,(
    ! [A_329,C_330] : k5_xboole_0(A_329,k5_xboole_0(A_329,C_330)) = C_330 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_3458])).

tff(c_3515,plain,(
    k5_xboole_0('#skF_5',k3_xboole_0('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3286,c_3479])).

tff(c_3528,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3479])).

tff(c_3639,plain,(
    k5_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_3')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3515,c_3528])).

tff(c_3476,plain,(
    ! [A_32,C_328] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_328)) = C_328 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_3458])).

tff(c_3930,plain,(
    k5_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3639,c_3476])).

tff(c_4077,plain,(
    k5_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4073,c_3930])).

tff(c_4083,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_4077])).

tff(c_4085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2431,c_4083])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.81  
% 4.23/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.23/1.81  
% 4.23/1.81  %Foreground sorts:
% 4.23/1.81  
% 4.23/1.81  
% 4.23/1.81  %Background operators:
% 4.23/1.81  
% 4.23/1.81  
% 4.23/1.81  %Foreground operators:
% 4.23/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.23/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.23/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.23/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.23/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.23/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.23/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.23/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.23/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.23/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.23/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.23/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.23/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.23/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.23/1.81  
% 4.47/1.83  tff(f_130, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.47/1.83  tff(f_74, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.47/1.83  tff(f_109, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.47/1.83  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.47/1.83  tff(f_66, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.47/1.83  tff(f_78, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.47/1.83  tff(f_76, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.47/1.83  tff(f_80, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.47/1.83  tff(f_64, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.47/1.83  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.47/1.83  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.47/1.83  tff(f_98, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.47/1.83  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.47/1.83  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.47/1.83  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.47/1.83  tff(c_70, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.47/1.83  tff(c_132, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_70])).
% 4.47/1.83  tff(c_68, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.47/1.83  tff(c_133, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_68])).
% 4.47/1.83  tff(c_74, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.47/1.83  tff(c_143, plain, (![A_80, B_81]: (r1_tarski(A_80, k2_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.83  tff(c_146, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_143])).
% 4.47/1.83  tff(c_594, plain, (![B_131, A_132]: (k1_tarski(B_131)=A_132 | k1_xboole_0=A_132 | ~r1_tarski(A_132, k1_tarski(B_131)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.47/1.83  tff(c_612, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_146, c_594])).
% 4.47/1.83  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_133, c_612])).
% 4.47/1.83  tff(c_632, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_68])).
% 4.47/1.83  tff(c_633, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_68])).
% 4.47/1.83  tff(c_72, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.47/1.83  tff(c_664, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_633, c_633, c_72])).
% 4.47/1.83  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.47/1.83  tff(c_665, plain, (![B_136, A_137]: (k5_xboole_0(B_136, A_137)=k5_xboole_0(A_137, B_136))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.47/1.83  tff(c_28, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.47/1.83  tff(c_681, plain, (![A_137]: (k5_xboole_0(k1_xboole_0, A_137)=A_137)), inference(superposition, [status(thm), theory('equality')], [c_665, c_28])).
% 4.47/1.83  tff(c_36, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.47/1.83  tff(c_1856, plain, (![A_228, B_229, C_230]: (k5_xboole_0(k5_xboole_0(A_228, B_229), C_230)=k5_xboole_0(A_228, k5_xboole_0(B_229, C_230)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.47/1.83  tff(c_1909, plain, (![A_32, C_230]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_230))=k5_xboole_0(k1_xboole_0, C_230))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1856])).
% 4.47/1.83  tff(c_1923, plain, (![A_231, C_232]: (k5_xboole_0(A_231, k5_xboole_0(A_231, C_232))=C_232)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_1909])).
% 4.47/1.83  tff(c_1963, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1923])).
% 4.47/1.83  tff(c_1985, plain, (![A_233, B_234]: (k5_xboole_0(A_233, k5_xboole_0(B_234, A_233))=B_234)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1923])).
% 4.47/1.83  tff(c_2012, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), B_2)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_1963, c_1985])).
% 4.47/1.83  tff(c_634, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_633, c_74])).
% 4.47/1.83  tff(c_2293, plain, (![A_241, B_242]: (k5_xboole_0(k5_xboole_0(A_241, B_242), k2_xboole_0(A_241, B_242))=k3_xboole_0(A_241, B_242))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.47/1.83  tff(c_2378, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_634, c_2293])).
% 4.47/1.83  tff(c_2395, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_2378])).
% 4.47/1.83  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(k3_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.47/1.83  tff(c_1180, plain, (![B_182, A_183]: (k1_tarski(B_182)=A_183 | k1_xboole_0=A_183 | ~r1_tarski(A_183, k1_tarski(B_182)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.47/1.83  tff(c_1187, plain, (![A_183]: (k1_tarski('#skF_3')=A_183 | k1_xboole_0=A_183 | ~r1_tarski(A_183, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_633, c_1180])).
% 4.47/1.83  tff(c_1206, plain, (![A_184]: (A_184='#skF_4' | k1_xboole_0=A_184 | ~r1_tarski(A_184, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_633, c_1187])).
% 4.47/1.83  tff(c_1227, plain, (![B_22]: (k3_xboole_0('#skF_4', B_22)='#skF_4' | k3_xboole_0('#skF_4', B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1206])).
% 4.47/1.83  tff(c_2404, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2395, c_1227])).
% 4.47/1.83  tff(c_2428, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2404])).
% 4.47/1.83  tff(c_2430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_632, c_664, c_2428])).
% 4.47/1.83  tff(c_2431, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_70])).
% 4.47/1.83  tff(c_2487, plain, (![B_249, A_250]: (k5_xboole_0(B_249, A_250)=k5_xboole_0(A_250, B_249))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.47/1.83  tff(c_2432, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 4.47/1.83  tff(c_2433, plain, (![A_23]: (k5_xboole_0(A_23, '#skF_4')=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_2432, c_28])).
% 4.47/1.83  tff(c_2503, plain, (![A_250]: (k5_xboole_0('#skF_4', A_250)=A_250)), inference(superposition, [status(thm), theory('equality')], [c_2487, c_2433])).
% 4.47/1.83  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.47/1.83  tff(c_3063, plain, (![A_313, B_314]: (r2_hidden('#skF_2'(A_313, B_314), k3_xboole_0(A_313, B_314)) | r1_xboole_0(A_313, B_314))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.47/1.83  tff(c_3080, plain, (![A_317]: (r2_hidden('#skF_2'(A_317, A_317), A_317) | r1_xboole_0(A_317, A_317))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3063])).
% 4.47/1.83  tff(c_56, plain, (![A_63, B_64]: (r1_tarski(k1_tarski(A_63), B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.47/1.83  tff(c_64, plain, (![B_68]: (r1_tarski(k1_xboole_0, k1_tarski(B_68)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.47/1.83  tff(c_2434, plain, (![B_68]: (r1_tarski('#skF_4', k1_tarski(B_68)))), inference(demodulation, [status(thm), theory('equality')], [c_2432, c_64])).
% 4.47/1.83  tff(c_2714, plain, (![B_280, A_281]: (B_280=A_281 | ~r1_tarski(B_280, A_281) | ~r1_tarski(A_281, B_280))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.47/1.83  tff(c_2733, plain, (![B_282]: (k1_tarski(B_282)='#skF_4' | ~r1_tarski(k1_tarski(B_282), '#skF_4'))), inference(resolution, [status(thm)], [c_2434, c_2714])).
% 4.47/1.83  tff(c_2738, plain, (![A_63]: (k1_tarski(A_63)='#skF_4' | ~r2_hidden(A_63, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_2733])).
% 4.47/1.83  tff(c_3092, plain, (k1_tarski('#skF_2'('#skF_4', '#skF_4'))='#skF_4' | r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3080, c_2738])).
% 4.47/1.83  tff(c_3094, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_3092])).
% 4.47/1.83  tff(c_2701, plain, (![A_276, B_277]: (r2_hidden('#skF_1'(A_276, B_277), A_276) | r1_tarski(A_276, B_277))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.47/1.83  tff(c_16, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.47/1.83  tff(c_2810, plain, (![A_288, B_289, B_290]: (~r1_xboole_0(A_288, B_289) | r1_tarski(k3_xboole_0(A_288, B_289), B_290))), inference(resolution, [status(thm)], [c_2701, c_16])).
% 4.47/1.83  tff(c_24, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.47/1.83  tff(c_3012, plain, (![A_310, B_311, B_312]: (k2_xboole_0(k3_xboole_0(A_310, B_311), B_312)=B_312 | ~r1_xboole_0(A_310, B_311))), inference(resolution, [status(thm)], [c_2810, c_24])).
% 4.47/1.83  tff(c_3053, plain, (![A_10, B_312]: (k2_xboole_0(A_10, B_312)=B_312 | ~r1_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3012])).
% 4.47/1.83  tff(c_3173, plain, (![B_312]: (k2_xboole_0('#skF_4', B_312)=B_312)), inference(resolution, [status(thm)], [c_3094, c_3053])).
% 4.47/1.83  tff(c_3213, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3173, c_74])).
% 4.47/1.83  tff(c_3215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2431, c_3213])).
% 4.47/1.83  tff(c_3216, plain, (k1_tarski('#skF_2'('#skF_4', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_3092])).
% 4.47/1.83  tff(c_60, plain, (![B_68, A_67]: (k1_tarski(B_68)=A_67 | k1_xboole_0=A_67 | ~r1_tarski(A_67, k1_tarski(B_68)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.47/1.83  tff(c_2739, plain, (![B_68, A_67]: (k1_tarski(B_68)=A_67 | A_67='#skF_4' | ~r1_tarski(A_67, k1_tarski(B_68)))), inference(demodulation, [status(thm), theory('equality')], [c_2432, c_60])).
% 4.47/1.83  tff(c_3331, plain, (![A_67]: (k1_tarski('#skF_2'('#skF_4', '#skF_4'))=A_67 | A_67='#skF_4' | ~r1_tarski(A_67, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3216, c_2739])).
% 4.47/1.83  tff(c_4054, plain, (![A_346]: (A_346='#skF_4' | A_346='#skF_4' | ~r1_tarski(A_346, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3216, c_3331])).
% 4.47/1.83  tff(c_4073, plain, (![B_22]: (k3_xboole_0('#skF_4', B_22)='#skF_4')), inference(resolution, [status(thm)], [c_26, c_4054])).
% 4.47/1.83  tff(c_3218, plain, (![A_322, B_323]: (k5_xboole_0(k5_xboole_0(A_322, B_323), k2_xboole_0(A_322, B_323))=k3_xboole_0(A_322, B_323))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.47/1.83  tff(c_3275, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_74, c_3218])).
% 4.47/1.83  tff(c_3286, plain, (k5_xboole_0('#skF_5', k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2503, c_3275])).
% 4.47/1.83  tff(c_2435, plain, (![A_32]: (k5_xboole_0(A_32, A_32)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2432, c_36])).
% 4.47/1.83  tff(c_3396, plain, (![A_326, B_327, C_328]: (k5_xboole_0(k5_xboole_0(A_326, B_327), C_328)=k5_xboole_0(A_326, k5_xboole_0(B_327, C_328)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.47/1.83  tff(c_3458, plain, (![A_32, C_328]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_328))=k5_xboole_0('#skF_4', C_328))), inference(superposition, [status(thm), theory('equality')], [c_2435, c_3396])).
% 4.47/1.83  tff(c_3479, plain, (![A_329, C_330]: (k5_xboole_0(A_329, k5_xboole_0(A_329, C_330))=C_330)), inference(demodulation, [status(thm), theory('equality')], [c_2503, c_3458])).
% 4.47/1.83  tff(c_3515, plain, (k5_xboole_0('#skF_5', k3_xboole_0('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3286, c_3479])).
% 4.47/1.83  tff(c_3528, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3479])).
% 4.47/1.83  tff(c_3639, plain, (k5_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_3'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3515, c_3528])).
% 4.47/1.83  tff(c_3476, plain, (![A_32, C_328]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_328))=C_328)), inference(demodulation, [status(thm), theory('equality')], [c_2503, c_3458])).
% 4.47/1.83  tff(c_3930, plain, (k5_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3639, c_3476])).
% 4.47/1.83  tff(c_4077, plain, (k5_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4073, c_3930])).
% 4.47/1.83  tff(c_4083, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2503, c_4077])).
% 4.47/1.83  tff(c_4085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2431, c_4083])).
% 4.47/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.83  
% 4.47/1.83  Inference rules
% 4.47/1.83  ----------------------
% 4.47/1.83  #Ref     : 0
% 4.47/1.83  #Sup     : 954
% 4.47/1.83  #Fact    : 1
% 4.47/1.83  #Define  : 0
% 4.47/1.83  #Split   : 5
% 4.47/1.83  #Chain   : 0
% 4.47/1.83  #Close   : 0
% 4.47/1.83  
% 4.47/1.83  Ordering : KBO
% 4.47/1.83  
% 4.47/1.83  Simplification rules
% 4.47/1.83  ----------------------
% 4.47/1.83  #Subsume      : 58
% 4.47/1.83  #Demod        : 465
% 4.47/1.83  #Tautology    : 570
% 4.47/1.83  #SimpNegUnit  : 21
% 4.47/1.83  #BackRed      : 13
% 4.47/1.83  
% 4.47/1.83  #Partial instantiations: 0
% 4.47/1.83  #Strategies tried      : 1
% 4.47/1.83  
% 4.47/1.83  Timing (in seconds)
% 4.47/1.83  ----------------------
% 4.47/1.83  Preprocessing        : 0.34
% 4.47/1.83  Parsing              : 0.18
% 4.47/1.83  CNF conversion       : 0.02
% 4.47/1.83  Main loop            : 0.71
% 4.47/1.83  Inferencing          : 0.25
% 4.47/1.83  Reduction            : 0.27
% 4.47/1.84  Demodulation         : 0.21
% 4.47/1.84  BG Simplification    : 0.03
% 4.47/1.84  Subsumption          : 0.11
% 4.47/1.84  Abstraction          : 0.04
% 4.47/1.84  MUC search           : 0.00
% 4.47/1.84  Cooper               : 0.00
% 4.47/1.84  Total                : 1.09
% 4.47/1.84  Index Insertion      : 0.00
% 4.47/1.84  Index Deletion       : 0.00
% 4.47/1.84  Index Matching       : 0.00
% 4.47/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
