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
% DateTime   : Thu Dec  3 09:50:00 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 704 expanded)
%              Number of leaves         :   31 ( 246 expanded)
%              Depth                    :   21
%              Number of atoms          :  147 (1651 expanded)
%              Number of equality atoms :   72 ( 818 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_82,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_62,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_194,plain,(
    ! [A_82,B_83] : k1_enumset1(A_82,A_82,B_83) = k2_tarski(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [E_27,A_21,C_23] : r2_hidden(E_27,k1_enumset1(A_21,E_27,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_212,plain,(
    ! [A_84,B_85] : r2_hidden(A_84,k2_tarski(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_42])).

tff(c_215,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_212])).

tff(c_279,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99,B_100),A_99)
      | r1_tarski(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [C_59] :
      ( C_59 = '#skF_5'
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_291,plain,(
    ! [B_101] :
      ( '#skF_1'('#skF_4',B_101) = '#skF_5'
      | r1_tarski('#skF_4',B_101) ) ),
    inference(resolution,[status(thm)],[c_279,c_78])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k4_xboole_0(B_20,A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_297,plain,(
    ! [B_20] :
      ( k1_xboole_0 = '#skF_4'
      | '#skF_1'('#skF_4',k4_xboole_0(B_20,'#skF_4')) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_291,c_36])).

tff(c_301,plain,(
    ! [B_20] : '#skF_1'('#skF_4',k4_xboole_0(B_20,'#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_297])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_290,plain,(
    ! [B_100] :
      ( '#skF_1'('#skF_4',B_100) = '#skF_5'
      | r1_tarski('#skF_4',B_100) ) ),
    inference(resolution,[status(thm)],[c_279,c_78])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_349,plain,(
    ! [C_105,B_106,A_107] :
      ( r2_hidden(C_105,B_106)
      | ~ r2_hidden(C_105,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_367,plain,(
    ! [A_3,B_4,B_106] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_106)
      | ~ r1_tarski(A_3,B_106)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_349])).

tff(c_64,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1257,plain,(
    ! [E_190,C_191,B_192,A_193] :
      ( E_190 = C_191
      | E_190 = B_192
      | E_190 = A_193
      | ~ r2_hidden(E_190,k1_enumset1(A_193,B_192,C_191)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1296,plain,(
    ! [E_194,B_195,A_196] :
      ( E_194 = B_195
      | E_194 = A_196
      | E_194 = A_196
      | ~ r2_hidden(E_194,k2_tarski(A_196,B_195)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1257])).

tff(c_1363,plain,(
    ! [E_201,A_202] :
      ( E_201 = A_202
      | E_201 = A_202
      | E_201 = A_202
      | ~ r2_hidden(E_201,k1_tarski(A_202)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1296])).

tff(c_1504,plain,(
    ! [A_215,A_216,B_217] :
      ( A_215 = '#skF_1'(A_216,B_217)
      | ~ r1_tarski(A_216,k1_tarski(A_215))
      | r1_tarski(A_216,B_217) ) ),
    inference(resolution,[status(thm)],[c_367,c_1363])).

tff(c_1574,plain,(
    ! [A_220,B_221] :
      ( A_220 = '#skF_1'('#skF_4',B_221)
      | r1_tarski('#skF_4',B_221)
      | '#skF_1'('#skF_4',k1_tarski(A_220)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_290,c_1504])).

tff(c_302,plain,(
    ! [B_102] : '#skF_1'('#skF_4',k4_xboole_0(B_102,'#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_297])).

tff(c_307,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_5','#skF_4')
      | r1_tarski('#skF_4',k4_xboole_0(B_102,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_10])).

tff(c_315,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_374,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_5',B_108)
      | ~ r1_tarski('#skF_4',B_108) ) ),
    inference(resolution,[status(thm)],[c_315,c_349])).

tff(c_6,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_381,plain,(
    ! [B_4,B_108] :
      ( r2_hidden('#skF_5',B_4)
      | ~ r1_tarski(B_108,B_4)
      | ~ r1_tarski('#skF_4',B_108) ) ),
    inference(resolution,[status(thm)],[c_374,c_6])).

tff(c_3185,plain,(
    ! [B_221,A_220] :
      ( r2_hidden('#skF_5',B_221)
      | ~ r1_tarski('#skF_4','#skF_4')
      | A_220 = '#skF_1'('#skF_4',B_221)
      | '#skF_1'('#skF_4',k1_tarski(A_220)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1574,c_381])).

tff(c_4129,plain,(
    ! [B_5564,A_5565] :
      ( r2_hidden('#skF_5',B_5564)
      | A_5565 = '#skF_1'('#skF_4',B_5564)
      | '#skF_1'('#skF_4',k1_tarski(A_5565)) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3185])).

tff(c_1321,plain,(
    ! [E_194,A_28] :
      ( E_194 = A_28
      | E_194 = A_28
      | E_194 = A_28
      | ~ r2_hidden(E_194,k1_tarski(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1296])).

tff(c_6777,plain,(
    ! [A_11134,A_11135] :
      ( A_11134 = '#skF_5'
      | A_11135 = '#skF_1'('#skF_4',k1_tarski(A_11134))
      | '#skF_1'('#skF_4',k1_tarski(A_11135)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_4129,c_1321])).

tff(c_8316,plain,(
    ! [A_11134,B_20] :
      ( '#skF_1'('#skF_4',k1_tarski(A_11134)) = '#skF_5'
      | A_11134 = '#skF_5'
      | '#skF_1'('#skF_4',k1_tarski('#skF_1'('#skF_4',k4_xboole_0(B_20,'#skF_4')))) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6777,c_301])).

tff(c_9129,plain,(
    ! [A_11134] :
      ( '#skF_1'('#skF_4',k1_tarski(A_11134)) = '#skF_5'
      | A_11134 = '#skF_5'
      | '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_8316])).

tff(c_9428,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9129])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9459,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9428,c_8])).

tff(c_9606,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_9459])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_9627,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9606,c_24])).

tff(c_9644,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_9627])).

tff(c_1389,plain,(
    ! [A_203,B_204] :
      ( '#skF_1'(k1_tarski(A_203),B_204) = A_203
      | r1_tarski(k1_tarski(A_203),B_204) ) ),
    inference(resolution,[status(thm)],[c_10,c_1363])).

tff(c_1435,plain,(
    ! [A_203,B_204] :
      ( k1_tarski(A_203) = B_204
      | ~ r1_tarski(B_204,k1_tarski(A_203))
      | '#skF_1'(k1_tarski(A_203),B_204) = A_203 ) ),
    inference(resolution,[status(thm)],[c_1389,c_24])).

tff(c_9616,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | '#skF_1'(k1_tarski('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9606,c_1435])).

tff(c_9633,plain,(
    '#skF_1'(k1_tarski('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_9616])).

tff(c_9686,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9633,c_8])).

tff(c_9772,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_9686])).

tff(c_9774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9644,c_9772])).

tff(c_9776,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9129])).

tff(c_1537,plain,(
    ! [A_215,B_217] :
      ( A_215 = '#skF_1'('#skF_4',B_217)
      | r1_tarski('#skF_4',B_217)
      | '#skF_1'('#skF_4',k1_tarski(A_215)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_290,c_1504])).

tff(c_9798,plain,(
    ! [A_215] :
      ( A_215 != '#skF_5'
      | r1_tarski('#skF_4',k1_tarski('#skF_5'))
      | '#skF_1'('#skF_4',k1_tarski(A_215)) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1537,c_9776])).

tff(c_10446,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_9798])).

tff(c_10462,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10446,c_24])).

tff(c_10479,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_10462])).

tff(c_10451,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | '#skF_1'(k1_tarski('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10446,c_1435])).

tff(c_10468,plain,(
    '#skF_1'(k1_tarski('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_10451])).

tff(c_10501,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10468,c_8])).

tff(c_10586,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_10501])).

tff(c_10588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10479,c_10586])).

tff(c_10590,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9798])).

tff(c_10618,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_290,c_10590])).

tff(c_10623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9776,c_10618])).

tff(c_10626,plain,(
    ! [B_18977] : r1_tarski('#skF_4',k4_xboole_0(B_18977,'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_10631,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10626,c_36])).

tff(c_10636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:22:50 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.39/2.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.59  
% 7.39/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.59  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.39/2.59  
% 7.39/2.59  %Foreground sorts:
% 7.39/2.59  
% 7.39/2.59  
% 7.39/2.59  %Background operators:
% 7.39/2.59  
% 7.39/2.59  
% 7.39/2.59  %Foreground operators:
% 7.39/2.59  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 7.39/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.39/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.39/2.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.39/2.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.39/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.39/2.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.39/2.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.39/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.39/2.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.39/2.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.39/2.59  tff('#skF_5', type, '#skF_5': $i).
% 7.39/2.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.39/2.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.39/2.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.39/2.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.39/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.39/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.39/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.39/2.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.39/2.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.39/2.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.39/2.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.39/2.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.39/2.59  
% 7.59/2.61  tff(f_106, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 7.59/2.61  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.59/2.61  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.59/2.61  tff(f_73, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.59/2.61  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.59/2.61  tff(f_58, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 7.59/2.61  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.59/2.61  tff(c_80, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.59/2.61  tff(c_82, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.59/2.61  tff(c_62, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.59/2.61  tff(c_194, plain, (![A_82, B_83]: (k1_enumset1(A_82, A_82, B_83)=k2_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.59/2.61  tff(c_42, plain, (![E_27, A_21, C_23]: (r2_hidden(E_27, k1_enumset1(A_21, E_27, C_23)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.59/2.61  tff(c_212, plain, (![A_84, B_85]: (r2_hidden(A_84, k2_tarski(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_42])).
% 7.59/2.61  tff(c_215, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_212])).
% 7.59/2.61  tff(c_279, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99, B_100), A_99) | r1_tarski(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.61  tff(c_78, plain, (![C_59]: (C_59='#skF_5' | ~r2_hidden(C_59, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.59/2.61  tff(c_291, plain, (![B_101]: ('#skF_1'('#skF_4', B_101)='#skF_5' | r1_tarski('#skF_4', B_101))), inference(resolution, [status(thm)], [c_279, c_78])).
% 7.59/2.61  tff(c_36, plain, (![A_19, B_20]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k4_xboole_0(B_20, A_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.59/2.61  tff(c_297, plain, (![B_20]: (k1_xboole_0='#skF_4' | '#skF_1'('#skF_4', k4_xboole_0(B_20, '#skF_4'))='#skF_5')), inference(resolution, [status(thm)], [c_291, c_36])).
% 7.59/2.61  tff(c_301, plain, (![B_20]: ('#skF_1'('#skF_4', k4_xboole_0(B_20, '#skF_4'))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_297])).
% 7.59/2.61  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.59/2.61  tff(c_290, plain, (![B_100]: ('#skF_1'('#skF_4', B_100)='#skF_5' | r1_tarski('#skF_4', B_100))), inference(resolution, [status(thm)], [c_279, c_78])).
% 7.59/2.61  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.61  tff(c_349, plain, (![C_105, B_106, A_107]: (r2_hidden(C_105, B_106) | ~r2_hidden(C_105, A_107) | ~r1_tarski(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.61  tff(c_367, plain, (![A_3, B_4, B_106]: (r2_hidden('#skF_1'(A_3, B_4), B_106) | ~r1_tarski(A_3, B_106) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_349])).
% 7.59/2.61  tff(c_64, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.59/2.61  tff(c_1257, plain, (![E_190, C_191, B_192, A_193]: (E_190=C_191 | E_190=B_192 | E_190=A_193 | ~r2_hidden(E_190, k1_enumset1(A_193, B_192, C_191)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.59/2.61  tff(c_1296, plain, (![E_194, B_195, A_196]: (E_194=B_195 | E_194=A_196 | E_194=A_196 | ~r2_hidden(E_194, k2_tarski(A_196, B_195)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1257])).
% 7.59/2.61  tff(c_1363, plain, (![E_201, A_202]: (E_201=A_202 | E_201=A_202 | E_201=A_202 | ~r2_hidden(E_201, k1_tarski(A_202)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1296])).
% 7.59/2.61  tff(c_1504, plain, (![A_215, A_216, B_217]: (A_215='#skF_1'(A_216, B_217) | ~r1_tarski(A_216, k1_tarski(A_215)) | r1_tarski(A_216, B_217))), inference(resolution, [status(thm)], [c_367, c_1363])).
% 7.59/2.61  tff(c_1574, plain, (![A_220, B_221]: (A_220='#skF_1'('#skF_4', B_221) | r1_tarski('#skF_4', B_221) | '#skF_1'('#skF_4', k1_tarski(A_220))='#skF_5')), inference(resolution, [status(thm)], [c_290, c_1504])).
% 7.59/2.61  tff(c_302, plain, (![B_102]: ('#skF_1'('#skF_4', k4_xboole_0(B_102, '#skF_4'))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_297])).
% 7.59/2.61  tff(c_307, plain, (![B_102]: (r2_hidden('#skF_5', '#skF_4') | r1_tarski('#skF_4', k4_xboole_0(B_102, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_302, c_10])).
% 7.59/2.61  tff(c_315, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_307])).
% 7.59/2.61  tff(c_374, plain, (![B_108]: (r2_hidden('#skF_5', B_108) | ~r1_tarski('#skF_4', B_108))), inference(resolution, [status(thm)], [c_315, c_349])).
% 7.59/2.61  tff(c_6, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.61  tff(c_381, plain, (![B_4, B_108]: (r2_hidden('#skF_5', B_4) | ~r1_tarski(B_108, B_4) | ~r1_tarski('#skF_4', B_108))), inference(resolution, [status(thm)], [c_374, c_6])).
% 7.59/2.61  tff(c_3185, plain, (![B_221, A_220]: (r2_hidden('#skF_5', B_221) | ~r1_tarski('#skF_4', '#skF_4') | A_220='#skF_1'('#skF_4', B_221) | '#skF_1'('#skF_4', k1_tarski(A_220))='#skF_5')), inference(resolution, [status(thm)], [c_1574, c_381])).
% 7.59/2.61  tff(c_4129, plain, (![B_5564, A_5565]: (r2_hidden('#skF_5', B_5564) | A_5565='#skF_1'('#skF_4', B_5564) | '#skF_1'('#skF_4', k1_tarski(A_5565))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3185])).
% 7.59/2.61  tff(c_1321, plain, (![E_194, A_28]: (E_194=A_28 | E_194=A_28 | E_194=A_28 | ~r2_hidden(E_194, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1296])).
% 7.59/2.61  tff(c_6777, plain, (![A_11134, A_11135]: (A_11134='#skF_5' | A_11135='#skF_1'('#skF_4', k1_tarski(A_11134)) | '#skF_1'('#skF_4', k1_tarski(A_11135))='#skF_5')), inference(resolution, [status(thm)], [c_4129, c_1321])).
% 7.59/2.61  tff(c_8316, plain, (![A_11134, B_20]: ('#skF_1'('#skF_4', k1_tarski(A_11134))='#skF_5' | A_11134='#skF_5' | '#skF_1'('#skF_4', k1_tarski('#skF_1'('#skF_4', k4_xboole_0(B_20, '#skF_4'))))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6777, c_301])).
% 7.59/2.61  tff(c_9129, plain, (![A_11134]: ('#skF_1'('#skF_4', k1_tarski(A_11134))='#skF_5' | A_11134='#skF_5' | '#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_8316])).
% 7.59/2.61  tff(c_9428, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(splitLeft, [status(thm)], [c_9129])).
% 7.59/2.61  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.61  tff(c_9459, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9428, c_8])).
% 7.59/2.61  tff(c_9606, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_9459])).
% 7.59/2.61  tff(c_24, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.59/2.61  tff(c_9627, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_9606, c_24])).
% 7.59/2.61  tff(c_9644, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_9627])).
% 7.59/2.61  tff(c_1389, plain, (![A_203, B_204]: ('#skF_1'(k1_tarski(A_203), B_204)=A_203 | r1_tarski(k1_tarski(A_203), B_204))), inference(resolution, [status(thm)], [c_10, c_1363])).
% 7.59/2.61  tff(c_1435, plain, (![A_203, B_204]: (k1_tarski(A_203)=B_204 | ~r1_tarski(B_204, k1_tarski(A_203)) | '#skF_1'(k1_tarski(A_203), B_204)=A_203)), inference(resolution, [status(thm)], [c_1389, c_24])).
% 7.59/2.61  tff(c_9616, plain, (k1_tarski('#skF_5')='#skF_4' | '#skF_1'(k1_tarski('#skF_5'), '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_9606, c_1435])).
% 7.59/2.61  tff(c_9633, plain, ('#skF_1'(k1_tarski('#skF_5'), '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_82, c_9616])).
% 7.59/2.61  tff(c_9686, plain, (~r2_hidden('#skF_5', '#skF_4') | r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9633, c_8])).
% 7.59/2.61  tff(c_9772, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_9686])).
% 7.59/2.61  tff(c_9774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9644, c_9772])).
% 7.59/2.61  tff(c_9776, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))!='#skF_5'), inference(splitRight, [status(thm)], [c_9129])).
% 7.59/2.61  tff(c_1537, plain, (![A_215, B_217]: (A_215='#skF_1'('#skF_4', B_217) | r1_tarski('#skF_4', B_217) | '#skF_1'('#skF_4', k1_tarski(A_215))='#skF_5')), inference(resolution, [status(thm)], [c_290, c_1504])).
% 7.59/2.61  tff(c_9798, plain, (![A_215]: (A_215!='#skF_5' | r1_tarski('#skF_4', k1_tarski('#skF_5')) | '#skF_1'('#skF_4', k1_tarski(A_215))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1537, c_9776])).
% 7.59/2.61  tff(c_10446, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_9798])).
% 7.59/2.61  tff(c_10462, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10446, c_24])).
% 7.59/2.61  tff(c_10479, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_10462])).
% 7.59/2.61  tff(c_10451, plain, (k1_tarski('#skF_5')='#skF_4' | '#skF_1'(k1_tarski('#skF_5'), '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_10446, c_1435])).
% 7.59/2.61  tff(c_10468, plain, ('#skF_1'(k1_tarski('#skF_5'), '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_82, c_10451])).
% 7.59/2.61  tff(c_10501, plain, (~r2_hidden('#skF_5', '#skF_4') | r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10468, c_8])).
% 7.59/2.61  tff(c_10586, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_10501])).
% 7.59/2.61  tff(c_10588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10479, c_10586])).
% 7.59/2.61  tff(c_10590, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_9798])).
% 7.59/2.61  tff(c_10618, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_290, c_10590])).
% 7.59/2.61  tff(c_10623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9776, c_10618])).
% 7.59/2.61  tff(c_10626, plain, (![B_18977]: (r1_tarski('#skF_4', k4_xboole_0(B_18977, '#skF_4')))), inference(splitRight, [status(thm)], [c_307])).
% 7.59/2.61  tff(c_10631, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10626, c_36])).
% 7.59/2.61  tff(c_10636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_10631])).
% 7.59/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.61  
% 7.59/2.61  Inference rules
% 7.59/2.61  ----------------------
% 7.59/2.61  #Ref     : 0
% 7.59/2.61  #Sup     : 1986
% 7.59/2.61  #Fact    : 2
% 7.59/2.61  #Define  : 0
% 7.59/2.61  #Split   : 3
% 7.59/2.61  #Chain   : 0
% 7.59/2.61  #Close   : 0
% 7.59/2.61  
% 7.59/2.61  Ordering : KBO
% 7.59/2.61  
% 7.59/2.61  Simplification rules
% 7.59/2.61  ----------------------
% 7.59/2.61  #Subsume      : 909
% 7.59/2.61  #Demod        : 145
% 7.59/2.61  #Tautology    : 240
% 7.59/2.61  #SimpNegUnit  : 17
% 7.59/2.61  #BackRed      : 0
% 7.59/2.61  
% 7.59/2.61  #Partial instantiations: 6555
% 7.59/2.61  #Strategies tried      : 1
% 7.59/2.61  
% 7.59/2.61  Timing (in seconds)
% 7.59/2.61  ----------------------
% 7.59/2.61  Preprocessing        : 0.34
% 7.59/2.61  Parsing              : 0.17
% 7.59/2.61  CNF conversion       : 0.03
% 7.59/2.61  Main loop            : 1.48
% 7.59/2.61  Inferencing          : 0.56
% 7.59/2.62  Reduction            : 0.43
% 7.59/2.62  Demodulation         : 0.31
% 7.59/2.62  BG Simplification    : 0.05
% 7.59/2.62  Subsumption          : 0.37
% 7.59/2.62  Abstraction          : 0.06
% 7.59/2.62  MUC search           : 0.00
% 7.59/2.62  Cooper               : 0.00
% 7.59/2.62  Total                : 1.86
% 7.59/2.62  Index Insertion      : 0.00
% 7.59/2.62  Index Deletion       : 0.00
% 7.59/2.62  Index Matching       : 0.00
% 7.59/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
