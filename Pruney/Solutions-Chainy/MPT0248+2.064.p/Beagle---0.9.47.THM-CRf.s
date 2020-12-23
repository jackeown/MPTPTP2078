%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:13 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 262 expanded)
%              Number of leaves         :   40 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 481 expanded)
%              Number of equality atoms :   59 ( 308 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_77,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_73,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_54,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_80,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1539,plain,(
    ! [B_151,A_152] :
      ( k3_xboole_0(B_151,k1_tarski(A_152)) = k1_tarski(A_152)
      | ~ r2_hidden(A_152,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_58,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_81,plain,(
    ! [A_68,B_69] : r1_tarski(A_68,k2_xboole_0(A_68,B_69)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_84,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_81])).

tff(c_176,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_186,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84,c_176])).

tff(c_1579,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1539,c_186])).

tff(c_1617,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1579])).

tff(c_46,plain,(
    ! [A_58,B_59] :
      ( r1_xboole_0(k1_tarski(A_58),B_59)
      | r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_945,plain,(
    ! [A_120,B_121,C_122] :
      ( ~ r1_xboole_0(A_120,B_121)
      | ~ r2_hidden(C_122,k3_xboole_0(A_120,B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4466,plain,(
    ! [B_258,A_259,C_260] :
      ( ~ r1_xboole_0(B_258,A_259)
      | ~ r2_hidden(C_260,k3_xboole_0(A_259,B_258)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_945])).

tff(c_4496,plain,(
    ! [C_260] :
      ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
      | ~ r2_hidden(C_260,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_4466])).

tff(c_4602,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4496])).

tff(c_4605,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_4602])).

tff(c_4609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1617,c_4605])).

tff(c_4610,plain,(
    ! [C_260] : ~ r2_hidden(C_260,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4496])).

tff(c_954,plain,(
    ! [C_122] :
      ( ~ r1_xboole_0('#skF_4',k1_tarski('#skF_3'))
      | ~ r2_hidden(C_122,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_945])).

tff(c_975,plain,(
    ~ r1_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_954])).

tff(c_2141,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166,B_167),k3_xboole_0(A_166,B_167))
      | r1_xboole_0(A_166,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2162,plain,
    ( r2_hidden('#skF_1'('#skF_4',k1_tarski('#skF_3')),'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2141])).

tff(c_2173,plain,(
    r2_hidden('#skF_1'('#skF_4',k1_tarski('#skF_3')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_2162])).

tff(c_4613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4610,c_2173])).

tff(c_4616,plain,(
    ! [C_268] : ~ r2_hidden(C_268,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_954])).

tff(c_4620,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_4616])).

tff(c_4624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4620])).

tff(c_4625,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_30,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4626,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4773,plain,(
    ! [A_281,B_282] :
      ( k4_xboole_0(A_281,B_282) = '#skF_4'
      | ~ r1_tarski(A_281,B_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_12])).

tff(c_4853,plain,(
    ! [A_287,B_288] : k4_xboole_0(A_287,k2_xboole_0(A_287,B_288)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_4773])).

tff(c_26,plain,(
    ! [A_25,B_26] : r1_tarski(k4_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4863,plain,(
    ! [A_287] : r1_tarski('#skF_4',A_287) ),
    inference(superposition,[status(thm),theory(equality)],[c_4853,c_26])).

tff(c_5037,plain,(
    ! [A_301,B_302] :
      ( k2_xboole_0(A_301,B_302) = B_302
      | ~ r1_tarski(A_301,B_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5055,plain,(
    ! [A_287] : k2_xboole_0('#skF_4',A_287) = A_287 ),
    inference(resolution,[status(thm)],[c_4863,c_5037])).

tff(c_5058,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5055,c_58])).

tff(c_5060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4625,c_5058])).

tff(c_5061,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5062,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5088,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5062,c_5062,c_56])).

tff(c_5366,plain,(
    ! [A_320,B_321] :
      ( r1_xboole_0(k1_tarski(A_320),B_321)
      | r2_hidden(A_320,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5369,plain,(
    ! [B_321] :
      ( r1_xboole_0('#skF_4',B_321)
      | r2_hidden('#skF_3',B_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5062,c_5366])).

tff(c_6255,plain,(
    ! [B_364,A_365] :
      ( k3_xboole_0(B_364,k1_tarski(A_365)) = k1_tarski(A_365)
      | ~ r2_hidden(A_365,B_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6312,plain,(
    ! [B_364] :
      ( k3_xboole_0(B_364,'#skF_4') = k1_tarski('#skF_3')
      | ~ r2_hidden('#skF_3',B_364) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5062,c_6255])).

tff(c_6524,plain,(
    ! [B_376] :
      ( k3_xboole_0(B_376,'#skF_4') = '#skF_4'
      | ~ r2_hidden('#skF_3',B_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5062,c_6312])).

tff(c_6528,plain,(
    ! [B_321] :
      ( k3_xboole_0(B_321,'#skF_4') = '#skF_4'
      | r1_xboole_0('#skF_4',B_321) ) ),
    inference(resolution,[status(thm)],[c_5369,c_6524])).

tff(c_28,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_24] : k3_xboole_0(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5726,plain,(
    ! [A_342,B_343] : k5_xboole_0(A_342,k3_xboole_0(A_342,B_343)) = k4_xboole_0(A_342,B_343) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5753,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = k4_xboole_0(A_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5726])).

tff(c_5761,plain,(
    ! [A_344] : k4_xboole_0(A_344,k1_xboole_0) = A_344 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5753])).

tff(c_5781,plain,(
    ! [A_344] : r1_tarski(A_344,A_344) ),
    inference(superposition,[status(thm),theory(equality)],[c_5761,c_26])).

tff(c_5063,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5062,c_58])).

tff(c_6030,plain,(
    ! [A_356,C_357,B_358] :
      ( r1_tarski(A_356,k2_xboole_0(C_357,B_358))
      | ~ r1_tarski(A_356,B_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6138,plain,(
    ! [A_363] :
      ( r1_tarski(A_363,'#skF_4')
      | ~ r1_tarski(A_363,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5063,c_6030])).

tff(c_6165,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5781,c_6138])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6179,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6165,c_22])).

tff(c_6203,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6179,c_2])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6331,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_7,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6203,c_6])).

tff(c_7610,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6331])).

tff(c_7614,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6528,c_7610])).

tff(c_7615,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7614,c_6179])).

tff(c_7617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5088,c_7615])).

tff(c_7620,plain,(
    ! [C_432] : ~ r2_hidden(C_432,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_6331])).

tff(c_7628,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8,c_7620])).

tff(c_7633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5061,c_7628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.04  
% 5.26/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.26/2.04  
% 5.26/2.04  %Foreground sorts:
% 5.26/2.04  
% 5.26/2.04  
% 5.26/2.04  %Background operators:
% 5.26/2.04  
% 5.26/2.04  
% 5.26/2.04  %Foreground operators:
% 5.26/2.04  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.26/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.26/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.26/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.26/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.26/2.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.26/2.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.26/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/2.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.26/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.26/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.26/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.26/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.26/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.26/2.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.26/2.04  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.26/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/2.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.26/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.26/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.26/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.26/2.04  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.26/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.26/2.04  
% 5.26/2.06  tff(f_123, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.26/2.06  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.26/2.06  tff(f_102, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 5.26/2.06  tff(f_79, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.26/2.06  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.26/2.06  tff(f_98, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.26/2.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.26/2.06  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.26/2.06  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.26/2.06  tff(f_75, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.26/2.06  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.26/2.06  tff(f_77, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.26/2.06  tff(f_73, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.26/2.06  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.26/2.06  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.26/2.06  tff(c_54, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.26/2.06  tff(c_94, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_54])).
% 5.26/2.06  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.26/2.06  tff(c_52, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.26/2.06  tff(c_80, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_52])).
% 5.26/2.06  tff(c_1539, plain, (![B_151, A_152]: (k3_xboole_0(B_151, k1_tarski(A_152))=k1_tarski(A_152) | ~r2_hidden(A_152, B_151))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.26/2.06  tff(c_58, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.26/2.06  tff(c_81, plain, (![A_68, B_69]: (r1_tarski(A_68, k2_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.26/2.06  tff(c_84, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_81])).
% 5.26/2.06  tff(c_176, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.26/2.06  tff(c_186, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_84, c_176])).
% 5.26/2.06  tff(c_1579, plain, (k1_tarski('#skF_3')='#skF_4' | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1539, c_186])).
% 5.26/2.06  tff(c_1617, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_1579])).
% 5.26/2.06  tff(c_46, plain, (![A_58, B_59]: (r1_xboole_0(k1_tarski(A_58), B_59) | r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.26/2.06  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.26/2.06  tff(c_945, plain, (![A_120, B_121, C_122]: (~r1_xboole_0(A_120, B_121) | ~r2_hidden(C_122, k3_xboole_0(A_120, B_121)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.26/2.06  tff(c_4466, plain, (![B_258, A_259, C_260]: (~r1_xboole_0(B_258, A_259) | ~r2_hidden(C_260, k3_xboole_0(A_259, B_258)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_945])).
% 5.26/2.06  tff(c_4496, plain, (![C_260]: (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | ~r2_hidden(C_260, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_4466])).
% 5.26/2.06  tff(c_4602, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4496])).
% 5.26/2.06  tff(c_4605, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_4602])).
% 5.26/2.06  tff(c_4609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1617, c_4605])).
% 5.26/2.06  tff(c_4610, plain, (![C_260]: (~r2_hidden(C_260, '#skF_4'))), inference(splitRight, [status(thm)], [c_4496])).
% 5.26/2.06  tff(c_954, plain, (![C_122]: (~r1_xboole_0('#skF_4', k1_tarski('#skF_3')) | ~r2_hidden(C_122, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_945])).
% 5.26/2.06  tff(c_975, plain, (~r1_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_954])).
% 5.26/2.06  tff(c_2141, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166, B_167), k3_xboole_0(A_166, B_167)) | r1_xboole_0(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.26/2.06  tff(c_2162, plain, (r2_hidden('#skF_1'('#skF_4', k1_tarski('#skF_3')), '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_2141])).
% 5.26/2.06  tff(c_2173, plain, (r2_hidden('#skF_1'('#skF_4', k1_tarski('#skF_3')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_975, c_2162])).
% 5.26/2.06  tff(c_4613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4610, c_2173])).
% 5.26/2.06  tff(c_4616, plain, (![C_268]: (~r2_hidden(C_268, '#skF_4'))), inference(splitRight, [status(thm)], [c_954])).
% 5.26/2.06  tff(c_4620, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_4616])).
% 5.26/2.06  tff(c_4624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_4620])).
% 5.26/2.06  tff(c_4625, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 5.26/2.06  tff(c_30, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.26/2.06  tff(c_4626, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 5.26/2.06  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.26/2.06  tff(c_4773, plain, (![A_281, B_282]: (k4_xboole_0(A_281, B_282)='#skF_4' | ~r1_tarski(A_281, B_282))), inference(demodulation, [status(thm), theory('equality')], [c_4626, c_12])).
% 5.26/2.06  tff(c_4853, plain, (![A_287, B_288]: (k4_xboole_0(A_287, k2_xboole_0(A_287, B_288))='#skF_4')), inference(resolution, [status(thm)], [c_30, c_4773])).
% 5.26/2.06  tff(c_26, plain, (![A_25, B_26]: (r1_tarski(k4_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.26/2.06  tff(c_4863, plain, (![A_287]: (r1_tarski('#skF_4', A_287))), inference(superposition, [status(thm), theory('equality')], [c_4853, c_26])).
% 5.26/2.06  tff(c_5037, plain, (![A_301, B_302]: (k2_xboole_0(A_301, B_302)=B_302 | ~r1_tarski(A_301, B_302))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.26/2.06  tff(c_5055, plain, (![A_287]: (k2_xboole_0('#skF_4', A_287)=A_287)), inference(resolution, [status(thm)], [c_4863, c_5037])).
% 5.26/2.06  tff(c_5058, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5055, c_58])).
% 5.26/2.06  tff(c_5060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4625, c_5058])).
% 5.26/2.06  tff(c_5061, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 5.26/2.06  tff(c_5062, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 5.26/2.06  tff(c_56, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.26/2.06  tff(c_5088, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5062, c_5062, c_56])).
% 5.26/2.06  tff(c_5366, plain, (![A_320, B_321]: (r1_xboole_0(k1_tarski(A_320), B_321) | r2_hidden(A_320, B_321))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.26/2.06  tff(c_5369, plain, (![B_321]: (r1_xboole_0('#skF_4', B_321) | r2_hidden('#skF_3', B_321))), inference(superposition, [status(thm), theory('equality')], [c_5062, c_5366])).
% 5.26/2.06  tff(c_6255, plain, (![B_364, A_365]: (k3_xboole_0(B_364, k1_tarski(A_365))=k1_tarski(A_365) | ~r2_hidden(A_365, B_364))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.26/2.06  tff(c_6312, plain, (![B_364]: (k3_xboole_0(B_364, '#skF_4')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', B_364))), inference(superposition, [status(thm), theory('equality')], [c_5062, c_6255])).
% 5.26/2.06  tff(c_6524, plain, (![B_376]: (k3_xboole_0(B_376, '#skF_4')='#skF_4' | ~r2_hidden('#skF_3', B_376))), inference(demodulation, [status(thm), theory('equality')], [c_5062, c_6312])).
% 5.26/2.06  tff(c_6528, plain, (![B_321]: (k3_xboole_0(B_321, '#skF_4')='#skF_4' | r1_xboole_0('#skF_4', B_321))), inference(resolution, [status(thm)], [c_5369, c_6524])).
% 5.26/2.06  tff(c_28, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=A_27)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.26/2.06  tff(c_24, plain, (![A_24]: (k3_xboole_0(A_24, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.26/2.06  tff(c_5726, plain, (![A_342, B_343]: (k5_xboole_0(A_342, k3_xboole_0(A_342, B_343))=k4_xboole_0(A_342, B_343))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.26/2.06  tff(c_5753, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=k4_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5726])).
% 5.26/2.06  tff(c_5761, plain, (![A_344]: (k4_xboole_0(A_344, k1_xboole_0)=A_344)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5753])).
% 5.26/2.06  tff(c_5781, plain, (![A_344]: (r1_tarski(A_344, A_344))), inference(superposition, [status(thm), theory('equality')], [c_5761, c_26])).
% 5.26/2.06  tff(c_5063, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5062, c_58])).
% 5.26/2.06  tff(c_6030, plain, (![A_356, C_357, B_358]: (r1_tarski(A_356, k2_xboole_0(C_357, B_358)) | ~r1_tarski(A_356, B_358))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.26/2.06  tff(c_6138, plain, (![A_363]: (r1_tarski(A_363, '#skF_4') | ~r1_tarski(A_363, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5063, c_6030])).
% 5.26/2.06  tff(c_6165, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5781, c_6138])).
% 5.26/2.06  tff(c_22, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.26/2.06  tff(c_6179, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_6165, c_22])).
% 5.26/2.06  tff(c_6203, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6179, c_2])).
% 5.26/2.06  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.26/2.06  tff(c_6331, plain, (![C_7]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_7, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6203, c_6])).
% 5.26/2.06  tff(c_7610, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_6331])).
% 5.26/2.06  tff(c_7614, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6528, c_7610])).
% 5.26/2.06  tff(c_7615, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7614, c_6179])).
% 5.26/2.06  tff(c_7617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5088, c_7615])).
% 5.26/2.06  tff(c_7620, plain, (![C_432]: (~r2_hidden(C_432, '#skF_5'))), inference(splitRight, [status(thm)], [c_6331])).
% 5.26/2.06  tff(c_7628, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8, c_7620])).
% 5.26/2.06  tff(c_7633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5061, c_7628])).
% 5.26/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.06  
% 5.26/2.06  Inference rules
% 5.26/2.06  ----------------------
% 5.26/2.06  #Ref     : 2
% 5.26/2.06  #Sup     : 1873
% 5.26/2.06  #Fact    : 0
% 5.26/2.06  #Define  : 0
% 5.26/2.06  #Split   : 10
% 5.26/2.06  #Chain   : 0
% 5.26/2.06  #Close   : 0
% 5.26/2.06  
% 5.26/2.06  Ordering : KBO
% 5.26/2.06  
% 5.26/2.06  Simplification rules
% 5.26/2.06  ----------------------
% 5.26/2.06  #Subsume      : 195
% 5.26/2.06  #Demod        : 817
% 5.26/2.06  #Tautology    : 1256
% 5.26/2.06  #SimpNegUnit  : 21
% 5.26/2.06  #BackRed      : 18
% 5.26/2.06  
% 5.26/2.06  #Partial instantiations: 0
% 5.26/2.06  #Strategies tried      : 1
% 5.26/2.06  
% 5.26/2.06  Timing (in seconds)
% 5.26/2.06  ----------------------
% 5.26/2.06  Preprocessing        : 0.32
% 5.26/2.06  Parsing              : 0.18
% 5.26/2.06  CNF conversion       : 0.02
% 5.26/2.06  Main loop            : 0.97
% 5.26/2.06  Inferencing          : 0.31
% 5.26/2.06  Reduction            : 0.38
% 5.26/2.06  Demodulation         : 0.29
% 5.26/2.06  BG Simplification    : 0.04
% 5.26/2.06  Subsumption          : 0.16
% 5.26/2.06  Abstraction          : 0.04
% 5.26/2.07  MUC search           : 0.00
% 5.26/2.07  Cooper               : 0.00
% 5.26/2.07  Total                : 1.33
% 5.26/2.07  Index Insertion      : 0.00
% 5.26/2.07  Index Deletion       : 0.00
% 5.26/2.07  Index Matching       : 0.00
% 5.26/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
