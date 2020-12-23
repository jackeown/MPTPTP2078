%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:04 EST 2020

% Result     : Theorem 9.29s
% Output     : CNFRefutation 9.29s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 626 expanded)
%              Number of leaves         :   34 ( 217 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 (1137 expanded)
%              Number of equality atoms :   88 ( 664 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff(f_106,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_81,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_60,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_72,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_73,plain,(
    ! [A_46,B_47] : r1_tarski(A_46,k2_xboole_0(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_76,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_73])).

tff(c_616,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_624,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_616])).

tff(c_634,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_624])).

tff(c_499,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_2'(A_90,B_91),A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [C_28,A_24] :
      ( C_28 = A_24
      | ~ r2_hidden(C_28,k1_tarski(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4031,plain,(
    ! [A_204,B_205] :
      ( '#skF_2'(k1_tarski(A_204),B_205) = A_204
      | r1_tarski(k1_tarski(A_204),B_205) ) ),
    inference(resolution,[status(thm)],[c_499,c_30])).

tff(c_4060,plain,(
    '#skF_2'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4031,c_634])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4069,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4060,c_8])).

tff(c_4074,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_4069])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1247,plain,(
    ! [C_144,B_145,A_146] :
      ( r2_hidden(C_144,B_145)
      | ~ r2_hidden(C_144,A_146)
      | ~ r1_tarski(A_146,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3781,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_3'(A_195),B_196)
      | ~ r1_tarski(A_195,B_196)
      | k1_xboole_0 = A_195 ) ),
    inference(resolution,[status(thm)],[c_12,c_1247])).

tff(c_8062,plain,(
    ! [A_292,A_293] :
      ( A_292 = '#skF_3'(A_293)
      | ~ r1_tarski(A_293,k1_tarski(A_292))
      | k1_xboole_0 = A_293 ) ),
    inference(resolution,[status(thm)],[c_3781,c_30])).

tff(c_8116,plain,
    ( '#skF_3'('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_76,c_8062])).

tff(c_8140,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_8116])).

tff(c_8148,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_8140,c_12])).

tff(c_8153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_4074,c_8148])).

tff(c_8154,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_8589,plain,(
    ! [B_327,A_328] :
      ( B_327 = A_328
      | ~ r1_tarski(B_327,A_328)
      | ~ r1_tarski(A_328,B_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8603,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_8589])).

tff(c_8618,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8603])).

tff(c_9050,plain,(
    ! [A_363,B_364] :
      ( r2_hidden('#skF_2'(A_363,B_364),A_363)
      | r1_tarski(A_363,B_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12008,plain,(
    ! [A_442,B_443] :
      ( '#skF_2'(k1_tarski(A_442),B_443) = A_442
      | r1_tarski(k1_tarski(A_442),B_443) ) ),
    inference(resolution,[status(thm)],[c_9050,c_30])).

tff(c_12033,plain,(
    '#skF_2'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12008,c_8618])).

tff(c_12042,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12033,c_8])).

tff(c_12047,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_8618,c_12042])).

tff(c_18,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8246,plain,(
    ! [A_303,B_304] :
      ( k2_xboole_0(A_303,B_304) = B_304
      | ~ r1_tarski(A_303,B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8258,plain,(
    ! [B_13] : k2_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_18,c_8246])).

tff(c_22,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8280,plain,(
    ! [A_306,B_307] : k3_tarski(k2_tarski(A_306,B_307)) = k2_xboole_0(A_306,B_307) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8317,plain,(
    ! [B_311,A_312] : k3_tarski(k2_tarski(B_311,A_312)) = k2_xboole_0(A_312,B_311) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8280])).

tff(c_50,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8344,plain,(
    ! [B_313,A_314] : k2_xboole_0(B_313,A_314) = k2_xboole_0(A_314,B_313) ),
    inference(superposition,[status(thm),theory(equality)],[c_8317,c_50])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8408,plain,(
    ! [A_317,B_318] : r1_tarski(A_317,k2_xboole_0(B_318,A_317)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8344,c_26])).

tff(c_8483,plain,(
    ! [B_322,A_323] : r1_tarski(k4_xboole_0(B_322,A_323),k2_xboole_0(A_323,B_322)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8408])).

tff(c_8516,plain,(
    ! [B_324] : r1_tarski(k4_xboole_0(B_324,B_324),B_324) ),
    inference(superposition,[status(thm),theory(equality)],[c_8258,c_8483])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8520,plain,(
    ! [B_324] : k2_xboole_0(k4_xboole_0(B_324,B_324),B_324) = B_324 ),
    inference(resolution,[status(thm)],[c_8516,c_20])).

tff(c_8414,plain,(
    ! [B_17,A_16] : r1_tarski(k4_xboole_0(B_17,A_16),k2_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8408])).

tff(c_8155,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_8201,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | A_10 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8155,c_12])).

tff(c_9542,plain,(
    ! [C_391,B_392,A_393] :
      ( r2_hidden(C_391,B_392)
      | ~ r2_hidden(C_391,A_393)
      | ~ r1_tarski(A_393,B_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12401,plain,(
    ! [A_455,B_456] :
      ( r2_hidden('#skF_3'(A_455),B_456)
      | ~ r1_tarski(A_455,B_456)
      | A_455 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_8201,c_9542])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12422,plain,(
    ! [B_458,A_459] :
      ( ~ v1_xboole_0(B_458)
      | ~ r1_tarski(A_459,B_458)
      | A_459 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_12401,c_2])).

tff(c_14209,plain,(
    ! [A_499,B_500] :
      ( ~ v1_xboole_0(k2_xboole_0(A_499,B_500))
      | k4_xboole_0(B_500,A_499) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_8414,c_12422])).

tff(c_14883,plain,(
    ! [B_517] :
      ( ~ v1_xboole_0(B_517)
      | k4_xboole_0(B_517,k4_xboole_0(B_517,B_517)) = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8520,c_14209])).

tff(c_8525,plain,(
    ! [B_325] : k2_xboole_0(k4_xboole_0(B_325,B_325),B_325) = B_325 ),
    inference(resolution,[status(thm)],[c_8516,c_20])).

tff(c_8531,plain,(
    ! [B_325] : r1_tarski(k4_xboole_0(B_325,k4_xboole_0(B_325,B_325)),B_325) ),
    inference(superposition,[status(thm),theory(equality)],[c_8525,c_8414])).

tff(c_14942,plain,(
    ! [B_518] :
      ( r1_tarski('#skF_7',B_518)
      | ~ v1_xboole_0(B_518) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14883,c_8531])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12121,plain,(
    ! [A_446,B_447] :
      ( r2_hidden('#skF_1'(A_446),B_447)
      | ~ r1_tarski(A_446,B_447)
      | v1_xboole_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_4,c_9542])).

tff(c_12136,plain,(
    ! [B_447,A_446] :
      ( ~ v1_xboole_0(B_447)
      | ~ r1_tarski(A_446,B_447)
      | v1_xboole_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_12121,c_2])).

tff(c_14967,plain,(
    ! [B_518] :
      ( v1_xboole_0('#skF_7')
      | ~ v1_xboole_0(B_518) ) ),
    inference(resolution,[status(thm)],[c_14942,c_12136])).

tff(c_14971,plain,(
    ! [B_518] : ~ v1_xboole_0(B_518) ),
    inference(splitLeft,[status(thm)],[c_14967])).

tff(c_9577,plain,(
    ! [A_1,B_392] :
      ( r2_hidden('#skF_1'(A_1),B_392)
      | ~ r1_tarski(A_1,B_392)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_9542])).

tff(c_14996,plain,(
    ! [A_521,B_522] :
      ( r2_hidden('#skF_1'(A_521),B_522)
      | ~ r1_tarski(A_521,B_522) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14971,c_9577])).

tff(c_15019,plain,(
    ! [A_523,A_524] :
      ( A_523 = '#skF_1'(A_524)
      | ~ r1_tarski(A_524,k1_tarski(A_523)) ) ),
    inference(resolution,[status(thm)],[c_14996,c_30])).

tff(c_15082,plain,(
    '#skF_1'('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_76,c_15019])).

tff(c_14980,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_14971,c_4])).

tff(c_15091,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15082,c_14980])).

tff(c_15095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12047,c_15091])).

tff(c_15096,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_14967])).

tff(c_9066,plain,(
    ! [A_365,B_366] :
      ( ~ v1_xboole_0(A_365)
      | r1_tarski(A_365,B_366) ) ),
    inference(resolution,[status(thm)],[c_9050,c_2])).

tff(c_9095,plain,(
    ! [A_365,B_366] :
      ( k2_xboole_0(A_365,B_366) = B_366
      | ~ v1_xboole_0(A_365) ) ),
    inference(resolution,[status(thm)],[c_9066,c_20])).

tff(c_15118,plain,(
    ! [B_366] : k2_xboole_0('#skF_7',B_366) = B_366 ),
    inference(resolution,[status(thm)],[c_15096,c_9095])).

tff(c_15243,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15118,c_64])).

tff(c_15245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8154,c_15243])).

tff(c_15247,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_15337,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15247,c_15247,c_62])).

tff(c_15393,plain,(
    ! [A_540,B_541] : k3_tarski(k2_tarski(A_540,B_541)) = k2_xboole_0(A_540,B_541) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_15531,plain,(
    ! [B_551,A_552] : k3_tarski(k2_tarski(B_551,A_552)) = k2_xboole_0(A_552,B_551) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_15393])).

tff(c_15558,plain,(
    ! [B_553,A_554] : k2_xboole_0(B_553,A_554) = k2_xboole_0(A_554,B_553) ),
    inference(superposition,[status(thm),theory(equality)],[c_15531,c_50])).

tff(c_15248,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15247,c_64])).

tff(c_15579,plain,(
    k2_xboole_0('#skF_8','#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_15558,c_15248])).

tff(c_15612,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15579,c_26])).

tff(c_16399,plain,(
    ! [B_603,A_604] :
      ( B_603 = A_604
      | ~ r1_tarski(B_603,A_604)
      | ~ r1_tarski(A_604,B_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16417,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_15612,c_16399])).

tff(c_16432,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_15337,c_16417])).

tff(c_15920,plain,(
    ! [A_576,B_577] :
      ( r2_hidden('#skF_2'(A_576,B_577),A_576)
      | r1_tarski(A_576,B_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15285,plain,(
    ! [C_531,A_532] :
      ( C_531 = A_532
      | ~ r2_hidden(C_531,k1_tarski(A_532)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_15288,plain,(
    ! [C_531] :
      ( C_531 = '#skF_6'
      | ~ r2_hidden(C_531,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15247,c_15285])).

tff(c_15975,plain,(
    ! [B_582] :
      ( '#skF_2'('#skF_7',B_582) = '#skF_6'
      | r1_tarski('#skF_7',B_582) ) ),
    inference(resolution,[status(thm)],[c_15920,c_15288])).

tff(c_16243,plain,(
    ! [B_598] :
      ( k2_xboole_0('#skF_7',B_598) = B_598
      | '#skF_2'('#skF_7',B_598) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_15975,c_20])).

tff(c_16291,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_2'('#skF_7','#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_16243,c_15248])).

tff(c_16328,plain,(
    '#skF_2'('#skF_7','#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_15337,c_16291])).

tff(c_16339,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r1_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_16328,c_8])).

tff(c_16687,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_16432,c_16339])).

tff(c_15246,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16589,plain,(
    ! [C_613,B_614,A_615] :
      ( r2_hidden(C_613,B_614)
      | ~ r2_hidden(C_613,A_615)
      | ~ r1_tarski(A_615,B_614) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19541,plain,(
    ! [A_708,B_709] :
      ( r2_hidden('#skF_1'(A_708),B_709)
      | ~ r1_tarski(A_708,B_709)
      | v1_xboole_0(A_708) ) ),
    inference(resolution,[status(thm)],[c_4,c_16589])).

tff(c_19756,plain,(
    ! [A_716] :
      ( '#skF_1'(A_716) = '#skF_6'
      | ~ r1_tarski(A_716,'#skF_7')
      | v1_xboole_0(A_716) ) ),
    inference(resolution,[status(thm)],[c_19541,c_15288])).

tff(c_19815,plain,
    ( '#skF_1'('#skF_8') = '#skF_6'
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_15612,c_19756])).

tff(c_19819,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_19815])).

tff(c_15338,plain,(
    ! [A_537] :
      ( r2_hidden('#skF_3'(A_537),A_537)
      | k1_xboole_0 = A_537 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15354,plain,(
    ! [A_537] :
      ( ~ v1_xboole_0(A_537)
      | k1_xboole_0 = A_537 ) ),
    inference(resolution,[status(thm)],[c_15338,c_2])).

tff(c_19833,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_19819,c_15354])).

tff(c_19843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15246,c_19833])).

tff(c_19845,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_19815])).

tff(c_19844,plain,(
    '#skF_1'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_19815])).

tff(c_19852,plain,
    ( v1_xboole_0('#skF_8')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_19844,c_4])).

tff(c_19857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16687,c_19845,c_19852])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:37:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.29/3.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.51  
% 9.29/3.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.52  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 9.29/3.52  
% 9.29/3.52  %Foreground sorts:
% 9.29/3.52  
% 9.29/3.52  
% 9.29/3.52  %Background operators:
% 9.29/3.52  
% 9.29/3.52  
% 9.29/3.52  %Foreground operators:
% 9.29/3.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.29/3.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.29/3.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.29/3.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.29/3.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.29/3.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.29/3.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.29/3.52  tff('#skF_7', type, '#skF_7': $i).
% 9.29/3.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.29/3.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.29/3.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.29/3.52  tff('#skF_6', type, '#skF_6': $i).
% 9.29/3.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.29/3.52  tff('#skF_8', type, '#skF_8': $i).
% 9.29/3.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.29/3.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.29/3.52  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.29/3.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.29/3.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.29/3.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.29/3.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.29/3.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.29/3.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.29/3.52  
% 9.29/3.54  tff(f_106, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 9.29/3.54  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.29/3.54  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.29/3.54  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.29/3.54  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.29/3.54  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.29/3.54  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.29/3.54  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.29/3.54  tff(f_64, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.29/3.54  tff(f_81, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.29/3.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.29/3.54  tff(c_60, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.29/3.54  tff(c_83, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_60])).
% 9.29/3.54  tff(c_58, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.29/3.54  tff(c_72, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_58])).
% 9.29/3.54  tff(c_64, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.29/3.54  tff(c_73, plain, (![A_46, B_47]: (r1_tarski(A_46, k2_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.29/3.54  tff(c_76, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_73])).
% 9.29/3.54  tff(c_616, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.29/3.54  tff(c_624, plain, (k1_tarski('#skF_6')='#skF_7' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_76, c_616])).
% 9.29/3.54  tff(c_634, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_624])).
% 9.29/3.54  tff(c_499, plain, (![A_90, B_91]: (r2_hidden('#skF_2'(A_90, B_91), A_90) | r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.29/3.54  tff(c_30, plain, (![C_28, A_24]: (C_28=A_24 | ~r2_hidden(C_28, k1_tarski(A_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.29/3.54  tff(c_4031, plain, (![A_204, B_205]: ('#skF_2'(k1_tarski(A_204), B_205)=A_204 | r1_tarski(k1_tarski(A_204), B_205))), inference(resolution, [status(thm)], [c_499, c_30])).
% 9.29/3.54  tff(c_4060, plain, ('#skF_2'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_4031, c_634])).
% 9.29/3.54  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.29/3.54  tff(c_4069, plain, (~r2_hidden('#skF_6', '#skF_7') | r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4060, c_8])).
% 9.29/3.54  tff(c_4074, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_634, c_4069])).
% 9.29/3.54  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.29/3.54  tff(c_1247, plain, (![C_144, B_145, A_146]: (r2_hidden(C_144, B_145) | ~r2_hidden(C_144, A_146) | ~r1_tarski(A_146, B_145))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.29/3.54  tff(c_3781, plain, (![A_195, B_196]: (r2_hidden('#skF_3'(A_195), B_196) | ~r1_tarski(A_195, B_196) | k1_xboole_0=A_195)), inference(resolution, [status(thm)], [c_12, c_1247])).
% 9.29/3.54  tff(c_8062, plain, (![A_292, A_293]: (A_292='#skF_3'(A_293) | ~r1_tarski(A_293, k1_tarski(A_292)) | k1_xboole_0=A_293)), inference(resolution, [status(thm)], [c_3781, c_30])).
% 9.29/3.54  tff(c_8116, plain, ('#skF_3'('#skF_7')='#skF_6' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_76, c_8062])).
% 9.29/3.54  tff(c_8140, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_83, c_8116])).
% 9.29/3.54  tff(c_8148, plain, (r2_hidden('#skF_6', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_8140, c_12])).
% 9.29/3.54  tff(c_8153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_4074, c_8148])).
% 9.29/3.54  tff(c_8154, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 9.29/3.54  tff(c_8589, plain, (![B_327, A_328]: (B_327=A_328 | ~r1_tarski(B_327, A_328) | ~r1_tarski(A_328, B_327))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.29/3.54  tff(c_8603, plain, (k1_tarski('#skF_6')='#skF_7' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_76, c_8589])).
% 9.29/3.54  tff(c_8618, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_8603])).
% 9.29/3.54  tff(c_9050, plain, (![A_363, B_364]: (r2_hidden('#skF_2'(A_363, B_364), A_363) | r1_tarski(A_363, B_364))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.29/3.54  tff(c_12008, plain, (![A_442, B_443]: ('#skF_2'(k1_tarski(A_442), B_443)=A_442 | r1_tarski(k1_tarski(A_442), B_443))), inference(resolution, [status(thm)], [c_9050, c_30])).
% 9.29/3.54  tff(c_12033, plain, ('#skF_2'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_12008, c_8618])).
% 9.29/3.54  tff(c_12042, plain, (~r2_hidden('#skF_6', '#skF_7') | r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12033, c_8])).
% 9.29/3.54  tff(c_12047, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_8618, c_12042])).
% 9.29/3.54  tff(c_18, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.29/3.54  tff(c_8246, plain, (![A_303, B_304]: (k2_xboole_0(A_303, B_304)=B_304 | ~r1_tarski(A_303, B_304))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.29/3.54  tff(c_8258, plain, (![B_13]: (k2_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_18, c_8246])).
% 9.29/3.54  tff(c_22, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.29/3.54  tff(c_28, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.29/3.54  tff(c_8280, plain, (![A_306, B_307]: (k3_tarski(k2_tarski(A_306, B_307))=k2_xboole_0(A_306, B_307))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.29/3.54  tff(c_8317, plain, (![B_311, A_312]: (k3_tarski(k2_tarski(B_311, A_312))=k2_xboole_0(A_312, B_311))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8280])).
% 9.29/3.54  tff(c_50, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.29/3.54  tff(c_8344, plain, (![B_313, A_314]: (k2_xboole_0(B_313, A_314)=k2_xboole_0(A_314, B_313))), inference(superposition, [status(thm), theory('equality')], [c_8317, c_50])).
% 9.29/3.54  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.29/3.54  tff(c_8408, plain, (![A_317, B_318]: (r1_tarski(A_317, k2_xboole_0(B_318, A_317)))), inference(superposition, [status(thm), theory('equality')], [c_8344, c_26])).
% 9.29/3.54  tff(c_8483, plain, (![B_322, A_323]: (r1_tarski(k4_xboole_0(B_322, A_323), k2_xboole_0(A_323, B_322)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8408])).
% 9.29/3.54  tff(c_8516, plain, (![B_324]: (r1_tarski(k4_xboole_0(B_324, B_324), B_324))), inference(superposition, [status(thm), theory('equality')], [c_8258, c_8483])).
% 9.29/3.54  tff(c_20, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.29/3.54  tff(c_8520, plain, (![B_324]: (k2_xboole_0(k4_xboole_0(B_324, B_324), B_324)=B_324)), inference(resolution, [status(thm)], [c_8516, c_20])).
% 9.29/3.54  tff(c_8414, plain, (![B_17, A_16]: (r1_tarski(k4_xboole_0(B_17, A_16), k2_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8408])).
% 9.29/3.54  tff(c_8155, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_60])).
% 9.29/3.54  tff(c_8201, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | A_10='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8155, c_12])).
% 9.29/3.54  tff(c_9542, plain, (![C_391, B_392, A_393]: (r2_hidden(C_391, B_392) | ~r2_hidden(C_391, A_393) | ~r1_tarski(A_393, B_392))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.29/3.54  tff(c_12401, plain, (![A_455, B_456]: (r2_hidden('#skF_3'(A_455), B_456) | ~r1_tarski(A_455, B_456) | A_455='#skF_7')), inference(resolution, [status(thm)], [c_8201, c_9542])).
% 9.29/3.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.29/3.54  tff(c_12422, plain, (![B_458, A_459]: (~v1_xboole_0(B_458) | ~r1_tarski(A_459, B_458) | A_459='#skF_7')), inference(resolution, [status(thm)], [c_12401, c_2])).
% 9.29/3.54  tff(c_14209, plain, (![A_499, B_500]: (~v1_xboole_0(k2_xboole_0(A_499, B_500)) | k4_xboole_0(B_500, A_499)='#skF_7')), inference(resolution, [status(thm)], [c_8414, c_12422])).
% 9.29/3.54  tff(c_14883, plain, (![B_517]: (~v1_xboole_0(B_517) | k4_xboole_0(B_517, k4_xboole_0(B_517, B_517))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8520, c_14209])).
% 9.29/3.54  tff(c_8525, plain, (![B_325]: (k2_xboole_0(k4_xboole_0(B_325, B_325), B_325)=B_325)), inference(resolution, [status(thm)], [c_8516, c_20])).
% 9.29/3.54  tff(c_8531, plain, (![B_325]: (r1_tarski(k4_xboole_0(B_325, k4_xboole_0(B_325, B_325)), B_325))), inference(superposition, [status(thm), theory('equality')], [c_8525, c_8414])).
% 9.29/3.54  tff(c_14942, plain, (![B_518]: (r1_tarski('#skF_7', B_518) | ~v1_xboole_0(B_518))), inference(superposition, [status(thm), theory('equality')], [c_14883, c_8531])).
% 9.29/3.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.29/3.54  tff(c_12121, plain, (![A_446, B_447]: (r2_hidden('#skF_1'(A_446), B_447) | ~r1_tarski(A_446, B_447) | v1_xboole_0(A_446))), inference(resolution, [status(thm)], [c_4, c_9542])).
% 9.29/3.54  tff(c_12136, plain, (![B_447, A_446]: (~v1_xboole_0(B_447) | ~r1_tarski(A_446, B_447) | v1_xboole_0(A_446))), inference(resolution, [status(thm)], [c_12121, c_2])).
% 9.29/3.54  tff(c_14967, plain, (![B_518]: (v1_xboole_0('#skF_7') | ~v1_xboole_0(B_518))), inference(resolution, [status(thm)], [c_14942, c_12136])).
% 9.29/3.54  tff(c_14971, plain, (![B_518]: (~v1_xboole_0(B_518))), inference(splitLeft, [status(thm)], [c_14967])).
% 9.29/3.54  tff(c_9577, plain, (![A_1, B_392]: (r2_hidden('#skF_1'(A_1), B_392) | ~r1_tarski(A_1, B_392) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_9542])).
% 9.29/3.54  tff(c_14996, plain, (![A_521, B_522]: (r2_hidden('#skF_1'(A_521), B_522) | ~r1_tarski(A_521, B_522))), inference(negUnitSimplification, [status(thm)], [c_14971, c_9577])).
% 9.29/3.54  tff(c_15019, plain, (![A_523, A_524]: (A_523='#skF_1'(A_524) | ~r1_tarski(A_524, k1_tarski(A_523)))), inference(resolution, [status(thm)], [c_14996, c_30])).
% 9.29/3.54  tff(c_15082, plain, ('#skF_1'('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_76, c_15019])).
% 9.29/3.54  tff(c_14980, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_14971, c_4])).
% 9.29/3.54  tff(c_15091, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15082, c_14980])).
% 9.29/3.54  tff(c_15095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12047, c_15091])).
% 9.29/3.54  tff(c_15096, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_14967])).
% 9.29/3.54  tff(c_9066, plain, (![A_365, B_366]: (~v1_xboole_0(A_365) | r1_tarski(A_365, B_366))), inference(resolution, [status(thm)], [c_9050, c_2])).
% 9.29/3.54  tff(c_9095, plain, (![A_365, B_366]: (k2_xboole_0(A_365, B_366)=B_366 | ~v1_xboole_0(A_365))), inference(resolution, [status(thm)], [c_9066, c_20])).
% 9.29/3.54  tff(c_15118, plain, (![B_366]: (k2_xboole_0('#skF_7', B_366)=B_366)), inference(resolution, [status(thm)], [c_15096, c_9095])).
% 9.29/3.54  tff(c_15243, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15118, c_64])).
% 9.29/3.54  tff(c_15245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8154, c_15243])).
% 9.29/3.54  tff(c_15247, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_58])).
% 9.29/3.54  tff(c_62, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.29/3.54  tff(c_15337, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15247, c_15247, c_62])).
% 9.29/3.54  tff(c_15393, plain, (![A_540, B_541]: (k3_tarski(k2_tarski(A_540, B_541))=k2_xboole_0(A_540, B_541))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.29/3.54  tff(c_15531, plain, (![B_551, A_552]: (k3_tarski(k2_tarski(B_551, A_552))=k2_xboole_0(A_552, B_551))), inference(superposition, [status(thm), theory('equality')], [c_28, c_15393])).
% 9.29/3.54  tff(c_15558, plain, (![B_553, A_554]: (k2_xboole_0(B_553, A_554)=k2_xboole_0(A_554, B_553))), inference(superposition, [status(thm), theory('equality')], [c_15531, c_50])).
% 9.29/3.54  tff(c_15248, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15247, c_64])).
% 9.29/3.54  tff(c_15579, plain, (k2_xboole_0('#skF_8', '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_15558, c_15248])).
% 9.29/3.54  tff(c_15612, plain, (r1_tarski('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15579, c_26])).
% 9.29/3.54  tff(c_16399, plain, (![B_603, A_604]: (B_603=A_604 | ~r1_tarski(B_603, A_604) | ~r1_tarski(A_604, B_603))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.29/3.54  tff(c_16417, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_15612, c_16399])).
% 9.29/3.54  tff(c_16432, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_15337, c_16417])).
% 9.29/3.54  tff(c_15920, plain, (![A_576, B_577]: (r2_hidden('#skF_2'(A_576, B_577), A_576) | r1_tarski(A_576, B_577))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.29/3.54  tff(c_15285, plain, (![C_531, A_532]: (C_531=A_532 | ~r2_hidden(C_531, k1_tarski(A_532)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.29/3.54  tff(c_15288, plain, (![C_531]: (C_531='#skF_6' | ~r2_hidden(C_531, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_15247, c_15285])).
% 9.29/3.54  tff(c_15975, plain, (![B_582]: ('#skF_2'('#skF_7', B_582)='#skF_6' | r1_tarski('#skF_7', B_582))), inference(resolution, [status(thm)], [c_15920, c_15288])).
% 9.29/3.54  tff(c_16243, plain, (![B_598]: (k2_xboole_0('#skF_7', B_598)=B_598 | '#skF_2'('#skF_7', B_598)='#skF_6')), inference(resolution, [status(thm)], [c_15975, c_20])).
% 9.29/3.54  tff(c_16291, plain, ('#skF_7'='#skF_8' | '#skF_2'('#skF_7', '#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_16243, c_15248])).
% 9.29/3.54  tff(c_16328, plain, ('#skF_2'('#skF_7', '#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_15337, c_16291])).
% 9.29/3.54  tff(c_16339, plain, (~r2_hidden('#skF_6', '#skF_8') | r1_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_16328, c_8])).
% 9.29/3.54  tff(c_16687, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_16432, c_16339])).
% 9.29/3.54  tff(c_15246, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 9.29/3.54  tff(c_16589, plain, (![C_613, B_614, A_615]: (r2_hidden(C_613, B_614) | ~r2_hidden(C_613, A_615) | ~r1_tarski(A_615, B_614))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.29/3.54  tff(c_19541, plain, (![A_708, B_709]: (r2_hidden('#skF_1'(A_708), B_709) | ~r1_tarski(A_708, B_709) | v1_xboole_0(A_708))), inference(resolution, [status(thm)], [c_4, c_16589])).
% 9.29/3.54  tff(c_19756, plain, (![A_716]: ('#skF_1'(A_716)='#skF_6' | ~r1_tarski(A_716, '#skF_7') | v1_xboole_0(A_716))), inference(resolution, [status(thm)], [c_19541, c_15288])).
% 9.29/3.54  tff(c_19815, plain, ('#skF_1'('#skF_8')='#skF_6' | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_15612, c_19756])).
% 9.29/3.54  tff(c_19819, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_19815])).
% 9.29/3.54  tff(c_15338, plain, (![A_537]: (r2_hidden('#skF_3'(A_537), A_537) | k1_xboole_0=A_537)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.29/3.54  tff(c_15354, plain, (![A_537]: (~v1_xboole_0(A_537) | k1_xboole_0=A_537)), inference(resolution, [status(thm)], [c_15338, c_2])).
% 9.29/3.54  tff(c_19833, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_19819, c_15354])).
% 9.29/3.54  tff(c_19843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15246, c_19833])).
% 9.29/3.54  tff(c_19845, plain, (~v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_19815])).
% 9.29/3.54  tff(c_19844, plain, ('#skF_1'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_19815])).
% 9.29/3.54  tff(c_19852, plain, (v1_xboole_0('#skF_8') | r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_19844, c_4])).
% 9.29/3.54  tff(c_19857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16687, c_19845, c_19852])).
% 9.29/3.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.54  
% 9.29/3.54  Inference rules
% 9.29/3.54  ----------------------
% 9.29/3.54  #Ref     : 0
% 9.29/3.54  #Sup     : 5033
% 9.29/3.54  #Fact    : 0
% 9.29/3.54  #Define  : 0
% 9.29/3.54  #Split   : 12
% 9.29/3.54  #Chain   : 0
% 9.29/3.54  #Close   : 0
% 9.50/3.54  
% 9.50/3.54  Ordering : KBO
% 9.50/3.54  
% 9.50/3.54  Simplification rules
% 9.50/3.54  ----------------------
% 9.50/3.54  #Subsume      : 1597
% 9.50/3.54  #Demod        : 3599
% 9.50/3.54  #Tautology    : 2338
% 9.50/3.54  #SimpNegUnit  : 212
% 9.50/3.54  #BackRed      : 23
% 9.50/3.54  
% 9.50/3.54  #Partial instantiations: 0
% 9.50/3.54  #Strategies tried      : 1
% 9.50/3.54  
% 9.50/3.54  Timing (in seconds)
% 9.50/3.54  ----------------------
% 9.50/3.54  Preprocessing        : 0.32
% 9.50/3.54  Parsing              : 0.15
% 9.50/3.54  CNF conversion       : 0.02
% 9.50/3.54  Main loop            : 2.32
% 9.50/3.54  Inferencing          : 0.60
% 9.50/3.54  Reduction            : 1.09
% 9.50/3.54  Demodulation         : 0.87
% 9.50/3.54  BG Simplification    : 0.06
% 9.50/3.54  Subsumption          : 0.43
% 9.50/3.54  Abstraction          : 0.09
% 9.50/3.54  MUC search           : 0.00
% 9.50/3.54  Cooper               : 0.00
% 9.50/3.54  Total                : 2.69
% 9.50/3.54  Index Insertion      : 0.00
% 9.50/3.54  Index Deletion       : 0.00
% 9.50/3.54  Index Matching       : 0.00
% 9.50/3.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
