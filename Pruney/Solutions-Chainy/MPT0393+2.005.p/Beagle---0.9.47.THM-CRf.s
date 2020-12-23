%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:17 EST 2020

% Result     : Theorem 10.39s
% Output     : CNFRefutation 10.39s
% Verified   : 
% Statistics : Number of formulae       :  145 (1206 expanded)
%              Number of leaves         :   32 ( 395 expanded)
%              Depth                    :   23
%              Number of atoms          :  224 (2587 expanded)
%              Number of equality atoms :  108 (1151 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_8 > #skF_9 > #skF_4 > #skF_5 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_103,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_84,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_91,axiom,(
    ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_setfam_1)).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    ! [B_33] : r1_tarski(k1_xboole_0,k1_tarski(B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_230,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1494,plain,(
    ! [A_3896,B_3897,B_3898] :
      ( r2_hidden('#skF_1'(A_3896,B_3897),B_3898)
      | ~ r1_tarski(A_3896,B_3898)
      | r1_tarski(A_3896,B_3897) ) ),
    inference(resolution,[status(thm)],[c_6,c_230])).

tff(c_56,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_21251,plain,(
    ! [A_76351,A_76352,B_76353] :
      ( A_76351 = '#skF_1'(A_76352,B_76353)
      | ~ r1_tarski(A_76352,k1_tarski(A_76351))
      | r1_tarski(A_76352,B_76353) ) ),
    inference(resolution,[status(thm)],[c_1494,c_56])).

tff(c_21311,plain,(
    ! [B_76428,B_76429] :
      ( B_76428 = '#skF_1'(k1_xboole_0,B_76429)
      | r1_tarski(k1_xboole_0,B_76429) ) ),
    inference(resolution,[status(thm)],[c_78,c_21251])).

tff(c_92,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2269,plain,(
    ! [A_7047,A_7048,B_7049] :
      ( A_7047 = '#skF_1'(A_7048,B_7049)
      | ~ r1_tarski(A_7048,k1_tarski(A_7047))
      | r1_tarski(A_7048,B_7049) ) ),
    inference(resolution,[status(thm)],[c_1494,c_56])).

tff(c_2297,plain,(
    ! [B_7266,B_7267] :
      ( B_7266 = '#skF_1'(k1_xboole_0,B_7267)
      | r1_tarski(k1_xboole_0,B_7267) ) ),
    inference(resolution,[status(thm)],[c_78,c_2269])).

tff(c_80,plain,(
    ! [A_34] : k3_tarski(k1_tarski(A_34)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3335,plain,(
    ! [B_10407] :
      ( k3_tarski('#skF_1'(k1_xboole_0,B_10407)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_10407) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_80])).

tff(c_2911,plain,(
    ! [B_7267,A_34] :
      ( k3_tarski('#skF_1'(k1_xboole_0,B_7267)) = A_34
      | r1_tarski(k1_xboole_0,B_7267) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_80])).

tff(c_3338,plain,(
    ! [A_34,B_10407] :
      ( k1_xboole_0 = A_34
      | r1_tarski(k1_xboole_0,B_10407)
      | r1_tarski(k1_xboole_0,B_10407) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3335,c_2911])).

tff(c_4200,plain,(
    ! [B_10407] :
      ( r1_tarski(k1_xboole_0,B_10407)
      | r1_tarski(k1_xboole_0,B_10407) ) ),
    inference(splitLeft,[status(thm)],[c_3338])).

tff(c_4209,plain,(
    ! [B_10407] : r1_tarski(k1_xboole_0,B_10407) ),
    inference(factorization,[status(thm),theory(equality)],[c_4200])).

tff(c_4398,plain,(
    ! [A_14346,B_14347,C_14348] :
      ( r2_hidden('#skF_2'(A_14346,B_14347,C_14348),A_14346)
      | r2_hidden('#skF_3'(A_14346,B_14347,C_14348),C_14348)
      | k4_xboole_0(A_14346,B_14347) = C_14348 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4773,plain,(
    ! [A_15012,C_15013] :
      ( r2_hidden('#skF_3'(A_15012,A_15012,C_15013),C_15013)
      | k4_xboole_0(A_15012,A_15012) = C_15013 ) ),
    inference(resolution,[status(thm)],[c_4398,c_22])).

tff(c_162,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_296,plain,(
    ! [A_98,B_99] :
      ( '#skF_1'(k1_tarski(A_98),B_99) = A_98
      | r1_tarski(k1_tarski(A_98),B_99) ) ),
    inference(resolution,[status(thm)],[c_162,c_56])).

tff(c_179,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_190,plain,(
    ! [B_33] :
      ( k1_tarski(B_33) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_33),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_78,c_179])).

tff(c_331,plain,(
    ! [A_102] :
      ( k1_tarski(A_102) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_102),k1_xboole_0) = A_102 ) ),
    inference(resolution,[status(thm)],[c_296,c_190])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1013,plain,(
    ! [A_1649] :
      ( ~ r2_hidden(A_1649,k1_xboole_0)
      | r1_tarski(k1_tarski(A_1649),k1_xboole_0)
      | k1_tarski(A_1649) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_4])).

tff(c_1081,plain,(
    ! [A_1649] :
      ( ~ r2_hidden(A_1649,k1_xboole_0)
      | k1_tarski(A_1649) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1013,c_190])).

tff(c_5638,plain,(
    ! [A_16003] :
      ( k1_tarski('#skF_3'(A_16003,A_16003,k1_xboole_0)) = k1_xboole_0
      | k4_xboole_0(A_16003,A_16003) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4773,c_1081])).

tff(c_251,plain,(
    ! [C_25,B_86] :
      ( r2_hidden(C_25,B_86)
      | ~ r1_tarski(k1_tarski(C_25),B_86) ) ),
    inference(resolution,[status(thm)],[c_58,c_230])).

tff(c_5682,plain,(
    ! [A_16003,B_86] :
      ( r2_hidden('#skF_3'(A_16003,A_16003,k1_xboole_0),B_86)
      | ~ r1_tarski(k1_xboole_0,B_86)
      | k4_xboole_0(A_16003,A_16003) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5638,c_251])).

tff(c_5761,plain,(
    ! [A_16003,B_86] :
      ( r2_hidden('#skF_3'(A_16003,A_16003,k1_xboole_0),B_86)
      | k4_xboole_0(A_16003,A_16003) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4209,c_5682])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17794,plain,(
    ! [A_59118,B_59119,B_59120] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_59118,B_59119),B_59120),A_59118)
      | r1_tarski(k4_xboole_0(A_59118,B_59119),B_59120) ) ),
    inference(resolution,[status(thm)],[c_162,c_12])).

tff(c_17885,plain,(
    ! [A_59445,B_59446] : r1_tarski(k4_xboole_0(A_59445,B_59446),A_59445) ),
    inference(resolution,[status(thm)],[c_17794,c_4])).

tff(c_4242,plain,(
    ! [B_13801] : r1_tarski(k1_xboole_0,B_13801) ),
    inference(factorization,[status(thm),theory(equality)],[c_4200])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4278,plain,(
    ! [B_13801] :
      ( k1_xboole_0 = B_13801
      | ~ r1_tarski(B_13801,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4242,c_26])).

tff(c_17948,plain,(
    ! [B_59771] : k4_xboole_0(k1_xboole_0,B_59771) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17885,c_4278])).

tff(c_82,plain,(
    ! [B_36,A_35] :
      ( ~ r2_hidden(B_36,A_35)
      | k4_xboole_0(A_35,k1_tarski(B_36)) != A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18028,plain,(
    ! [B_60060] : ~ r2_hidden(B_60060,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_17948,c_82])).

tff(c_18100,plain,(
    ! [A_60313] : k4_xboole_0(A_60313,A_60313) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5761,c_18028])).

tff(c_18125,plain,(
    ! [B_36] :
      ( ~ r2_hidden(B_36,k1_tarski(B_36))
      | k1_tarski(B_36) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18100,c_82])).

tff(c_18151,plain,(
    ! [B_36] : k1_tarski(B_36) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18125])).

tff(c_371,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_8'(A_108,B_109),A_108)
      | r1_tarski(B_109,k1_setfam_1(A_108))
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_389,plain,(
    ! [A_21,B_109] :
      ( '#skF_8'(k1_tarski(A_21),B_109) = A_21
      | r1_tarski(B_109,k1_setfam_1(k1_tarski(A_21)))
      | k1_tarski(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_371,c_56])).

tff(c_18672,plain,(
    ! [A_62601,B_62602] :
      ( '#skF_8'(k1_tarski(A_62601),B_62602) = A_62601
      | r1_tarski(B_62602,k1_setfam_1(k1_tarski(A_62601))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18151,c_389])).

tff(c_86,plain,(
    ! [A_37] : r1_tarski(k1_setfam_1(A_37),k3_tarski(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_189,plain,(
    ! [A_37] :
      ( k3_tarski(A_37) = k1_setfam_1(A_37)
      | ~ r1_tarski(k3_tarski(A_37),k1_setfam_1(A_37)) ) ),
    inference(resolution,[status(thm)],[c_86,c_179])).

tff(c_18688,plain,(
    ! [A_62601] :
      ( k3_tarski(k1_tarski(A_62601)) = k1_setfam_1(k1_tarski(A_62601))
      | '#skF_8'(k1_tarski(A_62601),k3_tarski(k1_tarski(A_62601))) = A_62601 ) ),
    inference(resolution,[status(thm)],[c_18672,c_189])).

tff(c_18855,plain,(
    ! [A_62964] :
      ( k1_setfam_1(k1_tarski(A_62964)) = A_62964
      | '#skF_8'(k1_tarski(A_62964),A_62964) = A_62964 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_18688])).

tff(c_19018,plain,(
    '#skF_8'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_18855,c_92])).

tff(c_88,plain,(
    ! [B_39,A_38] :
      ( ~ r1_tarski(B_39,'#skF_8'(A_38,B_39))
      | r1_tarski(B_39,k1_setfam_1(A_38))
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_19034,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9')))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_19018,c_88])).

tff(c_19083,plain,
    ( r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9')))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_19034])).

tff(c_19084,plain,(
    r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_18151,c_19083])).

tff(c_366,plain,(
    ! [A_107] :
      ( k3_tarski(A_107) = k1_setfam_1(A_107)
      | ~ r1_tarski(k3_tarski(A_107),k1_setfam_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_86,c_179])).

tff(c_369,plain,(
    ! [A_34] :
      ( k3_tarski(k1_tarski(A_34)) = k1_setfam_1(k1_tarski(A_34))
      | ~ r1_tarski(A_34,k1_setfam_1(k1_tarski(A_34))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_366])).

tff(c_370,plain,(
    ! [A_34] :
      ( k1_setfam_1(k1_tarski(A_34)) = A_34
      | ~ r1_tarski(A_34,k1_setfam_1(k1_tarski(A_34))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_369])).

tff(c_19091,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_19084,c_370])).

tff(c_19141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_19091])).

tff(c_19144,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3338])).

tff(c_19142,plain,(
    ! [A_34] : k1_xboole_0 = A_34 ),
    inference(splitRight,[status(thm)],[c_3338])).

tff(c_19321,plain,(
    ! [A_65882] : A_65882 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_19144,c_19142])).

tff(c_107,plain,(
    ! [A_45] : r1_tarski(k1_setfam_1(A_45),k3_tarski(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_110,plain,(
    ! [A_34] : r1_tarski(k1_setfam_1(k1_tarski(A_34)),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_107])).

tff(c_279,plain,(
    ! [B_96,A_97] :
      ( k1_tarski(B_96) = A_97
      | k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,k1_tarski(B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_291,plain,(
    ! [B_96] :
      ( k1_setfam_1(k1_tarski(k1_tarski(B_96))) = k1_tarski(B_96)
      | k1_setfam_1(k1_tarski(k1_tarski(B_96))) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_279])).

tff(c_2144,plain,(
    ! [B_6938] :
      ( k1_setfam_1(k1_tarski(k1_tarski(B_6938))) = k1_xboole_0
      | k1_tarski(B_6938) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_291])).

tff(c_418,plain,(
    ! [A_119,B_120] :
      ( '#skF_6'(A_119,B_120) = A_119
      | '#skF_7'(A_119,B_120) != A_119
      | k1_tarski(A_119) = B_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_869,plain,(
    ! [B_120] :
      ( k1_setfam_1(B_120) != '#skF_9'
      | '#skF_6'('#skF_9',B_120) = '#skF_9'
      | '#skF_7'('#skF_9',B_120) != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_92])).

tff(c_2153,plain,(
    ! [B_6938] :
      ( k1_xboole_0 != '#skF_9'
      | '#skF_6'('#skF_9',k1_tarski(k1_tarski(B_6938))) = '#skF_9'
      | '#skF_7'('#skF_9',k1_tarski(k1_tarski(B_6938))) != '#skF_9'
      | k1_tarski(B_6938) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2144,c_869])).

tff(c_2296,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2153])).

tff(c_19479,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_19321,c_2296])).

tff(c_19481,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2153])).

tff(c_928,plain,(
    ! [A_119] :
      ( '#skF_6'(A_119,'#skF_9') = A_119
      | '#skF_7'(A_119,'#skF_9') != A_119
      | k1_tarski(A_119) = '#skF_9' ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_930,plain,(
    ! [A_119] :
      ( r1_tarski(k1_xboole_0,'#skF_9')
      | '#skF_6'(A_119,'#skF_9') = A_119
      | '#skF_7'(A_119,'#skF_9') != A_119 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_78])).

tff(c_1868,plain,(
    r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_930])).

tff(c_1871,plain,
    ( k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1868,c_26])).

tff(c_1872,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1871])).

tff(c_19484,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19481,c_1872])).

tff(c_19502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_19484])).

tff(c_19503,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1871])).

tff(c_19519,plain,(
    ! [B_33] : r1_tarski('#skF_9',k1_tarski(B_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19503,c_78])).

tff(c_1086,plain,(
    ! [A_1686] :
      ( ~ r2_hidden(A_1686,k1_xboole_0)
      | k1_tarski(A_1686) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1013,c_190])).

tff(c_1136,plain,(
    ! [B_1762] :
      ( k1_tarski('#skF_1'(k1_xboole_0,B_1762)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_1762) ) ),
    inference(resolution,[status(thm)],[c_6,c_1086])).

tff(c_1180,plain,(
    ! [B_1762] :
      ( k3_tarski(k1_xboole_0) = '#skF_1'(k1_xboole_0,B_1762)
      | r1_tarski(k1_xboole_0,B_1762) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_80])).

tff(c_19925,plain,(
    ! [B_68955] :
      ( k3_tarski('#skF_9') = '#skF_1'('#skF_9',B_68955)
      | r1_tarski('#skF_9',B_68955) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19503,c_19503,c_19503,c_1180])).

tff(c_19929,plain,
    ( k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9'
    | '#skF_1'('#skF_9',k1_setfam_1(k1_tarski('#skF_9'))) = k3_tarski('#skF_9') ),
    inference(resolution,[status(thm)],[c_19925,c_370])).

tff(c_19947,plain,(
    '#skF_1'('#skF_9',k1_setfam_1(k1_tarski('#skF_9'))) = k3_tarski('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_19929])).

tff(c_1114,plain,(
    ! [B_2] :
      ( k1_tarski('#skF_1'(k1_xboole_0,B_2)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1086])).

tff(c_19513,plain,(
    ! [B_2] :
      ( k1_tarski('#skF_1'('#skF_9',B_2)) = '#skF_9'
      | r1_tarski('#skF_9',B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19503,c_19503,c_19503,c_1114])).

tff(c_19952,plain,
    ( k1_tarski(k3_tarski('#skF_9')) = '#skF_9'
    | r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19947,c_19513])).

tff(c_20019,plain,(
    r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_19952])).

tff(c_20022,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_20019,c_370])).

tff(c_20066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_20022])).

tff(c_20067,plain,(
    k1_tarski(k3_tarski('#skF_9')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_19952])).

tff(c_20341,plain,(
    ! [B_69536] :
      ( r2_hidden(k3_tarski('#skF_9'),B_69536)
      | ~ r1_tarski('#skF_9',B_69536) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20067,c_251])).

tff(c_20370,plain,(
    ! [A_21] :
      ( k3_tarski('#skF_9') = A_21
      | ~ r1_tarski('#skF_9',k1_tarski(A_21)) ) ),
    inference(resolution,[status(thm)],[c_20341,c_56])).

tff(c_20420,plain,(
    k3_tarski('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19519,c_20370])).

tff(c_20405,plain,(
    ! [A_21] : k3_tarski('#skF_9') = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19519,c_20370])).

tff(c_20959,plain,(
    ! [A_73931] : A_73931 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_20420,c_20405])).

tff(c_20417,plain,(
    k3_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19519,c_20370])).

tff(c_20821,plain,(
    ! [A_71698] : k1_xboole_0 = A_71698 ),
    inference(superposition,[status(thm),theory(equality)],[c_20417,c_20405])).

tff(c_20952,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_20821,c_92])).

tff(c_21082,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_20959,c_20952])).

tff(c_21084,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_930])).

tff(c_22063,plain,(
    '#skF_1'(k1_xboole_0,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_21311,c_21084])).

tff(c_22050,plain,(
    ! [B_76428] : B_76428 = '#skF_1'(k1_xboole_0,'#skF_9') ),
    inference(resolution,[status(thm)],[c_21311,c_21084])).

tff(c_22503,plain,(
    ! [B_82912] : B_82912 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_22063,c_22050])).

tff(c_22536,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_22503,c_21084])).

tff(c_22646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.39/3.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.39/3.28  
% 10.39/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.39/3.28  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_8 > #skF_9 > #skF_4 > #skF_5 > #skF_3 > #skF_7 > #skF_1
% 10.39/3.28  
% 10.39/3.28  %Foreground sorts:
% 10.39/3.28  
% 10.39/3.28  
% 10.39/3.28  %Background operators:
% 10.39/3.28  
% 10.39/3.28  
% 10.39/3.28  %Foreground operators:
% 10.39/3.28  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.39/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.39/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.39/3.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.39/3.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.39/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.39/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.39/3.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.39/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.39/3.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.39/3.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.39/3.28  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 10.39/3.28  tff('#skF_9', type, '#skF_9': $i).
% 10.39/3.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.39/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.39/3.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.39/3.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 10.39/3.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.39/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.39/3.28  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 10.39/3.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.39/3.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.39/3.28  
% 10.39/3.30  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.39/3.30  tff(f_82, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 10.39/3.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.39/3.30  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 10.39/3.30  tff(f_103, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 10.39/3.30  tff(f_84, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 10.39/3.30  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.39/3.30  tff(f_89, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.39/3.30  tff(f_100, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 10.39/3.30  tff(f_91, axiom, (![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_setfam_1)).
% 10.39/3.30  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.39/3.30  tff(c_78, plain, (![B_33]: (r1_tarski(k1_xboole_0, k1_tarski(B_33)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.39/3.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.39/3.30  tff(c_230, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.39/3.30  tff(c_1494, plain, (![A_3896, B_3897, B_3898]: (r2_hidden('#skF_1'(A_3896, B_3897), B_3898) | ~r1_tarski(A_3896, B_3898) | r1_tarski(A_3896, B_3897))), inference(resolution, [status(thm)], [c_6, c_230])).
% 10.39/3.30  tff(c_56, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.39/3.30  tff(c_21251, plain, (![A_76351, A_76352, B_76353]: (A_76351='#skF_1'(A_76352, B_76353) | ~r1_tarski(A_76352, k1_tarski(A_76351)) | r1_tarski(A_76352, B_76353))), inference(resolution, [status(thm)], [c_1494, c_56])).
% 10.39/3.30  tff(c_21311, plain, (![B_76428, B_76429]: (B_76428='#skF_1'(k1_xboole_0, B_76429) | r1_tarski(k1_xboole_0, B_76429))), inference(resolution, [status(thm)], [c_78, c_21251])).
% 10.39/3.30  tff(c_92, plain, (k1_setfam_1(k1_tarski('#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.39/3.30  tff(c_58, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.39/3.30  tff(c_2269, plain, (![A_7047, A_7048, B_7049]: (A_7047='#skF_1'(A_7048, B_7049) | ~r1_tarski(A_7048, k1_tarski(A_7047)) | r1_tarski(A_7048, B_7049))), inference(resolution, [status(thm)], [c_1494, c_56])).
% 10.39/3.30  tff(c_2297, plain, (![B_7266, B_7267]: (B_7266='#skF_1'(k1_xboole_0, B_7267) | r1_tarski(k1_xboole_0, B_7267))), inference(resolution, [status(thm)], [c_78, c_2269])).
% 10.39/3.30  tff(c_80, plain, (![A_34]: (k3_tarski(k1_tarski(A_34))=A_34)), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.39/3.30  tff(c_3335, plain, (![B_10407]: (k3_tarski('#skF_1'(k1_xboole_0, B_10407))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_10407))), inference(superposition, [status(thm), theory('equality')], [c_2297, c_80])).
% 10.39/3.30  tff(c_2911, plain, (![B_7267, A_34]: (k3_tarski('#skF_1'(k1_xboole_0, B_7267))=A_34 | r1_tarski(k1_xboole_0, B_7267))), inference(superposition, [status(thm), theory('equality')], [c_2297, c_80])).
% 10.39/3.30  tff(c_3338, plain, (![A_34, B_10407]: (k1_xboole_0=A_34 | r1_tarski(k1_xboole_0, B_10407) | r1_tarski(k1_xboole_0, B_10407))), inference(superposition, [status(thm), theory('equality')], [c_3335, c_2911])).
% 10.39/3.30  tff(c_4200, plain, (![B_10407]: (r1_tarski(k1_xboole_0, B_10407) | r1_tarski(k1_xboole_0, B_10407))), inference(splitLeft, [status(thm)], [c_3338])).
% 10.39/3.30  tff(c_4209, plain, (![B_10407]: (r1_tarski(k1_xboole_0, B_10407))), inference(factorization, [status(thm), theory('equality')], [c_4200])).
% 10.39/3.30  tff(c_4398, plain, (![A_14346, B_14347, C_14348]: (r2_hidden('#skF_2'(A_14346, B_14347, C_14348), A_14346) | r2_hidden('#skF_3'(A_14346, B_14347, C_14348), C_14348) | k4_xboole_0(A_14346, B_14347)=C_14348)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.39/3.30  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.39/3.30  tff(c_4773, plain, (![A_15012, C_15013]: (r2_hidden('#skF_3'(A_15012, A_15012, C_15013), C_15013) | k4_xboole_0(A_15012, A_15012)=C_15013)), inference(resolution, [status(thm)], [c_4398, c_22])).
% 10.39/3.30  tff(c_162, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.39/3.30  tff(c_296, plain, (![A_98, B_99]: ('#skF_1'(k1_tarski(A_98), B_99)=A_98 | r1_tarski(k1_tarski(A_98), B_99))), inference(resolution, [status(thm)], [c_162, c_56])).
% 10.39/3.30  tff(c_179, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.39/3.30  tff(c_190, plain, (![B_33]: (k1_tarski(B_33)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_33), k1_xboole_0))), inference(resolution, [status(thm)], [c_78, c_179])).
% 10.39/3.30  tff(c_331, plain, (![A_102]: (k1_tarski(A_102)=k1_xboole_0 | '#skF_1'(k1_tarski(A_102), k1_xboole_0)=A_102)), inference(resolution, [status(thm)], [c_296, c_190])).
% 10.39/3.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.39/3.30  tff(c_1013, plain, (![A_1649]: (~r2_hidden(A_1649, k1_xboole_0) | r1_tarski(k1_tarski(A_1649), k1_xboole_0) | k1_tarski(A_1649)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_331, c_4])).
% 10.39/3.30  tff(c_1081, plain, (![A_1649]: (~r2_hidden(A_1649, k1_xboole_0) | k1_tarski(A_1649)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1013, c_190])).
% 10.39/3.30  tff(c_5638, plain, (![A_16003]: (k1_tarski('#skF_3'(A_16003, A_16003, k1_xboole_0))=k1_xboole_0 | k4_xboole_0(A_16003, A_16003)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4773, c_1081])).
% 10.39/3.30  tff(c_251, plain, (![C_25, B_86]: (r2_hidden(C_25, B_86) | ~r1_tarski(k1_tarski(C_25), B_86))), inference(resolution, [status(thm)], [c_58, c_230])).
% 10.39/3.30  tff(c_5682, plain, (![A_16003, B_86]: (r2_hidden('#skF_3'(A_16003, A_16003, k1_xboole_0), B_86) | ~r1_tarski(k1_xboole_0, B_86) | k4_xboole_0(A_16003, A_16003)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5638, c_251])).
% 10.39/3.30  tff(c_5761, plain, (![A_16003, B_86]: (r2_hidden('#skF_3'(A_16003, A_16003, k1_xboole_0), B_86) | k4_xboole_0(A_16003, A_16003)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4209, c_5682])).
% 10.39/3.30  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.39/3.30  tff(c_17794, plain, (![A_59118, B_59119, B_59120]: (r2_hidden('#skF_1'(k4_xboole_0(A_59118, B_59119), B_59120), A_59118) | r1_tarski(k4_xboole_0(A_59118, B_59119), B_59120))), inference(resolution, [status(thm)], [c_162, c_12])).
% 10.39/3.30  tff(c_17885, plain, (![A_59445, B_59446]: (r1_tarski(k4_xboole_0(A_59445, B_59446), A_59445))), inference(resolution, [status(thm)], [c_17794, c_4])).
% 10.39/3.30  tff(c_4242, plain, (![B_13801]: (r1_tarski(k1_xboole_0, B_13801))), inference(factorization, [status(thm), theory('equality')], [c_4200])).
% 10.39/3.30  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.39/3.30  tff(c_4278, plain, (![B_13801]: (k1_xboole_0=B_13801 | ~r1_tarski(B_13801, k1_xboole_0))), inference(resolution, [status(thm)], [c_4242, c_26])).
% 10.39/3.30  tff(c_17948, plain, (![B_59771]: (k4_xboole_0(k1_xboole_0, B_59771)=k1_xboole_0)), inference(resolution, [status(thm)], [c_17885, c_4278])).
% 10.39/3.30  tff(c_82, plain, (![B_36, A_35]: (~r2_hidden(B_36, A_35) | k4_xboole_0(A_35, k1_tarski(B_36))!=A_35)), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.39/3.30  tff(c_18028, plain, (![B_60060]: (~r2_hidden(B_60060, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_17948, c_82])).
% 10.39/3.30  tff(c_18100, plain, (![A_60313]: (k4_xboole_0(A_60313, A_60313)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5761, c_18028])).
% 10.39/3.30  tff(c_18125, plain, (![B_36]: (~r2_hidden(B_36, k1_tarski(B_36)) | k1_tarski(B_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18100, c_82])).
% 10.39/3.30  tff(c_18151, plain, (![B_36]: (k1_tarski(B_36)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18125])).
% 10.39/3.30  tff(c_371, plain, (![A_108, B_109]: (r2_hidden('#skF_8'(A_108, B_109), A_108) | r1_tarski(B_109, k1_setfam_1(A_108)) | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.39/3.30  tff(c_389, plain, (![A_21, B_109]: ('#skF_8'(k1_tarski(A_21), B_109)=A_21 | r1_tarski(B_109, k1_setfam_1(k1_tarski(A_21))) | k1_tarski(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_371, c_56])).
% 10.39/3.30  tff(c_18672, plain, (![A_62601, B_62602]: ('#skF_8'(k1_tarski(A_62601), B_62602)=A_62601 | r1_tarski(B_62602, k1_setfam_1(k1_tarski(A_62601))))), inference(negUnitSimplification, [status(thm)], [c_18151, c_389])).
% 10.39/3.30  tff(c_86, plain, (![A_37]: (r1_tarski(k1_setfam_1(A_37), k3_tarski(A_37)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.39/3.30  tff(c_189, plain, (![A_37]: (k3_tarski(A_37)=k1_setfam_1(A_37) | ~r1_tarski(k3_tarski(A_37), k1_setfam_1(A_37)))), inference(resolution, [status(thm)], [c_86, c_179])).
% 10.39/3.30  tff(c_18688, plain, (![A_62601]: (k3_tarski(k1_tarski(A_62601))=k1_setfam_1(k1_tarski(A_62601)) | '#skF_8'(k1_tarski(A_62601), k3_tarski(k1_tarski(A_62601)))=A_62601)), inference(resolution, [status(thm)], [c_18672, c_189])).
% 10.39/3.30  tff(c_18855, plain, (![A_62964]: (k1_setfam_1(k1_tarski(A_62964))=A_62964 | '#skF_8'(k1_tarski(A_62964), A_62964)=A_62964)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_18688])).
% 10.39/3.30  tff(c_19018, plain, ('#skF_8'(k1_tarski('#skF_9'), '#skF_9')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_18855, c_92])).
% 10.39/3.30  tff(c_88, plain, (![B_39, A_38]: (~r1_tarski(B_39, '#skF_8'(A_38, B_39)) | r1_tarski(B_39, k1_setfam_1(A_38)) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.39/3.30  tff(c_19034, plain, (~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9'))) | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_19018, c_88])).
% 10.39/3.30  tff(c_19083, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9'))) | k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_19034])).
% 10.39/3.30  tff(c_19084, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_18151, c_19083])).
% 10.39/3.30  tff(c_366, plain, (![A_107]: (k3_tarski(A_107)=k1_setfam_1(A_107) | ~r1_tarski(k3_tarski(A_107), k1_setfam_1(A_107)))), inference(resolution, [status(thm)], [c_86, c_179])).
% 10.39/3.30  tff(c_369, plain, (![A_34]: (k3_tarski(k1_tarski(A_34))=k1_setfam_1(k1_tarski(A_34)) | ~r1_tarski(A_34, k1_setfam_1(k1_tarski(A_34))))), inference(superposition, [status(thm), theory('equality')], [c_80, c_366])).
% 10.39/3.30  tff(c_370, plain, (![A_34]: (k1_setfam_1(k1_tarski(A_34))=A_34 | ~r1_tarski(A_34, k1_setfam_1(k1_tarski(A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_369])).
% 10.39/3.30  tff(c_19091, plain, (k1_setfam_1(k1_tarski('#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_19084, c_370])).
% 10.39/3.30  tff(c_19141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_19091])).
% 10.39/3.30  tff(c_19144, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_3338])).
% 10.39/3.30  tff(c_19142, plain, (![A_34]: (k1_xboole_0=A_34)), inference(splitRight, [status(thm)], [c_3338])).
% 10.39/3.30  tff(c_19321, plain, (![A_65882]: (A_65882='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_19144, c_19142])).
% 10.39/3.30  tff(c_107, plain, (![A_45]: (r1_tarski(k1_setfam_1(A_45), k3_tarski(A_45)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.39/3.30  tff(c_110, plain, (![A_34]: (r1_tarski(k1_setfam_1(k1_tarski(A_34)), A_34))), inference(superposition, [status(thm), theory('equality')], [c_80, c_107])).
% 10.39/3.30  tff(c_279, plain, (![B_96, A_97]: (k1_tarski(B_96)=A_97 | k1_xboole_0=A_97 | ~r1_tarski(A_97, k1_tarski(B_96)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.39/3.30  tff(c_291, plain, (![B_96]: (k1_setfam_1(k1_tarski(k1_tarski(B_96)))=k1_tarski(B_96) | k1_setfam_1(k1_tarski(k1_tarski(B_96)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_279])).
% 10.39/3.30  tff(c_2144, plain, (![B_6938]: (k1_setfam_1(k1_tarski(k1_tarski(B_6938)))=k1_xboole_0 | k1_tarski(B_6938)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_291])).
% 10.39/3.30  tff(c_418, plain, (![A_119, B_120]: ('#skF_6'(A_119, B_120)=A_119 | '#skF_7'(A_119, B_120)!=A_119 | k1_tarski(A_119)=B_120)), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.39/3.30  tff(c_869, plain, (![B_120]: (k1_setfam_1(B_120)!='#skF_9' | '#skF_6'('#skF_9', B_120)='#skF_9' | '#skF_7'('#skF_9', B_120)!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_418, c_92])).
% 10.39/3.30  tff(c_2153, plain, (![B_6938]: (k1_xboole_0!='#skF_9' | '#skF_6'('#skF_9', k1_tarski(k1_tarski(B_6938)))='#skF_9' | '#skF_7'('#skF_9', k1_tarski(k1_tarski(B_6938)))!='#skF_9' | k1_tarski(B_6938)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2144, c_869])).
% 10.39/3.30  tff(c_2296, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_2153])).
% 10.39/3.30  tff(c_19479, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_19321, c_2296])).
% 10.39/3.30  tff(c_19481, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_2153])).
% 10.39/3.30  tff(c_928, plain, (![A_119]: ('#skF_6'(A_119, '#skF_9')=A_119 | '#skF_7'(A_119, '#skF_9')!=A_119 | k1_tarski(A_119)='#skF_9')), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.39/3.30  tff(c_930, plain, (![A_119]: (r1_tarski(k1_xboole_0, '#skF_9') | '#skF_6'(A_119, '#skF_9')=A_119 | '#skF_7'(A_119, '#skF_9')!=A_119)), inference(superposition, [status(thm), theory('equality')], [c_928, c_78])).
% 10.39/3.30  tff(c_1868, plain, (r1_tarski(k1_xboole_0, '#skF_9')), inference(splitLeft, [status(thm)], [c_930])).
% 10.39/3.30  tff(c_1871, plain, (k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_1868, c_26])).
% 10.39/3.30  tff(c_1872, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1871])).
% 10.39/3.30  tff(c_19484, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_19481, c_1872])).
% 10.39/3.30  tff(c_19502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_19484])).
% 10.39/3.30  tff(c_19503, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1871])).
% 10.39/3.30  tff(c_19519, plain, (![B_33]: (r1_tarski('#skF_9', k1_tarski(B_33)))), inference(demodulation, [status(thm), theory('equality')], [c_19503, c_78])).
% 10.39/3.30  tff(c_1086, plain, (![A_1686]: (~r2_hidden(A_1686, k1_xboole_0) | k1_tarski(A_1686)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1013, c_190])).
% 10.39/3.30  tff(c_1136, plain, (![B_1762]: (k1_tarski('#skF_1'(k1_xboole_0, B_1762))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_1762))), inference(resolution, [status(thm)], [c_6, c_1086])).
% 10.39/3.30  tff(c_1180, plain, (![B_1762]: (k3_tarski(k1_xboole_0)='#skF_1'(k1_xboole_0, B_1762) | r1_tarski(k1_xboole_0, B_1762))), inference(superposition, [status(thm), theory('equality')], [c_1136, c_80])).
% 10.39/3.30  tff(c_19925, plain, (![B_68955]: (k3_tarski('#skF_9')='#skF_1'('#skF_9', B_68955) | r1_tarski('#skF_9', B_68955))), inference(demodulation, [status(thm), theory('equality')], [c_19503, c_19503, c_19503, c_1180])).
% 10.39/3.30  tff(c_19929, plain, (k1_setfam_1(k1_tarski('#skF_9'))='#skF_9' | '#skF_1'('#skF_9', k1_setfam_1(k1_tarski('#skF_9')))=k3_tarski('#skF_9')), inference(resolution, [status(thm)], [c_19925, c_370])).
% 10.39/3.30  tff(c_19947, plain, ('#skF_1'('#skF_9', k1_setfam_1(k1_tarski('#skF_9')))=k3_tarski('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_92, c_19929])).
% 10.39/3.30  tff(c_1114, plain, (![B_2]: (k1_tarski('#skF_1'(k1_xboole_0, B_2))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_1086])).
% 10.39/3.30  tff(c_19513, plain, (![B_2]: (k1_tarski('#skF_1'('#skF_9', B_2))='#skF_9' | r1_tarski('#skF_9', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_19503, c_19503, c_19503, c_1114])).
% 10.39/3.30  tff(c_19952, plain, (k1_tarski(k3_tarski('#skF_9'))='#skF_9' | r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_19947, c_19513])).
% 10.39/3.30  tff(c_20019, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_19952])).
% 10.39/3.30  tff(c_20022, plain, (k1_setfam_1(k1_tarski('#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_20019, c_370])).
% 10.39/3.30  tff(c_20066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_20022])).
% 10.39/3.30  tff(c_20067, plain, (k1_tarski(k3_tarski('#skF_9'))='#skF_9'), inference(splitRight, [status(thm)], [c_19952])).
% 10.39/3.30  tff(c_20341, plain, (![B_69536]: (r2_hidden(k3_tarski('#skF_9'), B_69536) | ~r1_tarski('#skF_9', B_69536))), inference(superposition, [status(thm), theory('equality')], [c_20067, c_251])).
% 10.39/3.30  tff(c_20370, plain, (![A_21]: (k3_tarski('#skF_9')=A_21 | ~r1_tarski('#skF_9', k1_tarski(A_21)))), inference(resolution, [status(thm)], [c_20341, c_56])).
% 10.39/3.30  tff(c_20420, plain, (k3_tarski('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_19519, c_20370])).
% 10.39/3.30  tff(c_20405, plain, (![A_21]: (k3_tarski('#skF_9')=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_19519, c_20370])).
% 10.39/3.30  tff(c_20959, plain, (![A_73931]: (A_73931='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_20420, c_20405])).
% 10.39/3.30  tff(c_20417, plain, (k3_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_19519, c_20370])).
% 10.39/3.30  tff(c_20821, plain, (![A_71698]: (k1_xboole_0=A_71698)), inference(superposition, [status(thm), theory('equality')], [c_20417, c_20405])).
% 10.39/3.30  tff(c_20952, plain, (k1_xboole_0!='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_20821, c_92])).
% 10.39/3.30  tff(c_21082, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_20959, c_20952])).
% 10.39/3.30  tff(c_21084, plain, (~r1_tarski(k1_xboole_0, '#skF_9')), inference(splitRight, [status(thm)], [c_930])).
% 10.39/3.30  tff(c_22063, plain, ('#skF_1'(k1_xboole_0, '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_21311, c_21084])).
% 10.39/3.30  tff(c_22050, plain, (![B_76428]: (B_76428='#skF_1'(k1_xboole_0, '#skF_9'))), inference(resolution, [status(thm)], [c_21311, c_21084])).
% 10.39/3.30  tff(c_22503, plain, (![B_82912]: (B_82912='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_22063, c_22050])).
% 10.39/3.30  tff(c_22536, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_22503, c_21084])).
% 10.39/3.30  tff(c_22646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_22536])).
% 10.39/3.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.39/3.30  
% 10.39/3.30  Inference rules
% 10.39/3.30  ----------------------
% 10.39/3.30  #Ref     : 0
% 10.39/3.30  #Sup     : 4015
% 10.39/3.30  #Fact    : 38
% 10.39/3.30  #Define  : 0
% 10.39/3.30  #Split   : 14
% 10.39/3.30  #Chain   : 0
% 10.39/3.30  #Close   : 0
% 10.39/3.30  
% 10.39/3.30  Ordering : KBO
% 10.39/3.30  
% 10.39/3.30  Simplification rules
% 10.39/3.30  ----------------------
% 10.39/3.30  #Subsume      : 759
% 10.39/3.30  #Demod        : 644
% 10.39/3.30  #Tautology    : 703
% 10.39/3.30  #SimpNegUnit  : 89
% 10.39/3.30  #BackRed      : 43
% 10.39/3.30  
% 10.39/3.30  #Partial instantiations: 31765
% 10.39/3.30  #Strategies tried      : 1
% 10.39/3.30  
% 10.39/3.30  Timing (in seconds)
% 10.39/3.30  ----------------------
% 10.39/3.30  Preprocessing        : 0.33
% 10.39/3.30  Parsing              : 0.16
% 10.39/3.30  CNF conversion       : 0.03
% 10.39/3.31  Main loop            : 2.19
% 10.39/3.31  Inferencing          : 1.13
% 10.39/3.31  Reduction            : 0.45
% 10.39/3.31  Demodulation         : 0.31
% 10.39/3.31  BG Simplification    : 0.08
% 10.39/3.31  Subsumption          : 0.37
% 10.39/3.31  Abstraction          : 0.09
% 10.39/3.31  MUC search           : 0.00
% 10.39/3.31  Cooper               : 0.00
% 10.39/3.31  Total                : 2.58
% 10.39/3.31  Index Insertion      : 0.00
% 10.39/3.31  Index Deletion       : 0.00
% 10.39/3.31  Index Matching       : 0.00
% 10.39/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
