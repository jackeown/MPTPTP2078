%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:15 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 190 expanded)
%              Number of leaves         :   41 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 320 expanded)
%              Number of equality atoms :   73 ( 269 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_74,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_116,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_72,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_105,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_127,plain,(
    ! [A_86,B_87] : r1_tarski(A_86,k2_xboole_0(A_86,B_87)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_130,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_127])).

tff(c_434,plain,(
    ! [B_142,A_143] :
      ( k1_tarski(B_142) = A_143
      | k1_xboole_0 = A_143
      | ~ r1_tarski(A_143,k1_tarski(B_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_437,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_130,c_434])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_105,c_437])).

tff(c_449,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_450,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_26,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_454,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_450,c_26])).

tff(c_804,plain,(
    ! [A_207,B_208,C_209] :
      ( ~ r1_xboole_0(A_207,B_208)
      | ~ r2_hidden(C_209,B_208)
      | ~ r2_hidden(C_209,A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_814,plain,(
    ! [C_210] : ~ r2_hidden(C_210,'#skF_4') ),
    inference(resolution,[status(thm)],[c_454,c_804])).

tff(c_859,plain,(
    ! [B_214] : r1_tarski('#skF_4',B_214) ),
    inference(resolution,[status(thm)],[c_8,c_814])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_869,plain,(
    ! [B_214] : k2_xboole_0('#skF_4',B_214) = B_214 ),
    inference(resolution,[status(thm)],[c_859,c_24])).

tff(c_1134,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_78])).

tff(c_1136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_1134])).

tff(c_1138,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1193,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_1138,c_76])).

tff(c_1137,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1143,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_78])).

tff(c_56,plain,(
    ! [A_70,B_71] :
      ( r1_xboole_0(k1_tarski(A_70),B_71)
      | r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1325,plain,(
    ! [A_245,B_246] :
      ( k3_xboole_0(A_245,B_246) = k1_xboole_0
      | ~ r1_xboole_0(A_245,B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1509,plain,(
    ! [A_281,B_282] :
      ( k3_xboole_0(k1_tarski(A_281),B_282) = k1_xboole_0
      | r2_hidden(A_281,B_282) ) ),
    inference(resolution,[status(thm)],[c_56,c_1325])).

tff(c_1522,plain,(
    ! [B_282] :
      ( k3_xboole_0('#skF_4',B_282) = k1_xboole_0
      | r2_hidden('#skF_3',B_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1138,c_1509])).

tff(c_42,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3047,plain,(
    ! [A_340,B_341,C_342] :
      ( r1_tarski(k2_tarski(A_340,B_341),C_342)
      | ~ r2_hidden(B_341,C_342)
      | ~ r2_hidden(A_340,C_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4868,plain,(
    ! [A_455,C_456] :
      ( r1_tarski(k1_tarski(A_455),C_456)
      | ~ r2_hidden(A_455,C_456)
      | ~ r2_hidden(A_455,C_456) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3047])).

tff(c_4896,plain,(
    ! [A_457,C_458] :
      ( k2_xboole_0(k1_tarski(A_457),C_458) = C_458
      | ~ r2_hidden(A_457,C_458) ) ),
    inference(resolution,[status(thm)],[c_4868,c_24])).

tff(c_5163,plain,(
    ! [C_464] :
      ( k2_xboole_0('#skF_4',C_464) = C_464
      | ~ r2_hidden('#skF_3',C_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1138,c_4896])).

tff(c_5966,plain,(
    ! [B_486] :
      ( k2_xboole_0('#skF_4',B_486) = B_486
      | k3_xboole_0('#skF_4',B_486) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1522,c_5163])).

tff(c_34,plain,(
    ! [A_27] : k5_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_10] : k2_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2185,plain,(
    ! [A_322,B_323] : k5_xboole_0(k5_xboole_0(A_322,B_323),k2_xboole_0(A_322,B_323)) = k3_xboole_0(A_322,B_323) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2258,plain,(
    ! [A_10] : k5_xboole_0(k5_xboole_0(A_10,A_10),A_10) = k3_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2185])).

tff(c_2270,plain,(
    ! [A_324] : k5_xboole_0(k1_xboole_0,A_324) = A_324 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16,c_2258])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2301,plain,(
    ! [A_324] : k5_xboole_0(A_324,k1_xboole_0) = A_324 ),
    inference(superposition,[status(thm),theory(equality)],[c_2270,c_2])).

tff(c_1868,plain,(
    ! [A_311,B_312,C_313] : k5_xboole_0(k5_xboole_0(A_311,B_312),C_313) = k5_xboole_0(A_311,k5_xboole_0(B_312,C_313)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1884,plain,(
    ! [A_311,B_312] : k5_xboole_0(A_311,k5_xboole_0(B_312,k5_xboole_0(A_311,B_312))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1868,c_34])).

tff(c_2265,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16,c_2258])).

tff(c_1907,plain,(
    ! [A_27,C_313] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_313)) = k5_xboole_0(k1_xboole_0,C_313) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1868])).

tff(c_2453,plain,(
    ! [A_326,C_327] : k5_xboole_0(A_326,k5_xboole_0(A_326,C_327)) = C_327 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2265,c_1907])).

tff(c_2509,plain,(
    ! [B_312,A_311] : k5_xboole_0(B_312,k5_xboole_0(A_311,B_312)) = k5_xboole_0(A_311,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1884,c_2453])).

tff(c_2543,plain,(
    ! [B_312,A_311] : k5_xboole_0(B_312,k5_xboole_0(A_311,B_312)) = A_311 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_2509])).

tff(c_2549,plain,(
    ! [B_328,A_329] : k5_xboole_0(B_328,k5_xboole_0(A_329,B_328)) = A_329 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_2509])).

tff(c_2579,plain,(
    ! [A_311,B_312] : k5_xboole_0(k5_xboole_0(A_311,B_312),A_311) = B_312 ),
    inference(superposition,[status(thm),theory(equality)],[c_2543,c_2549])).

tff(c_2255,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_2185])).

tff(c_2917,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_2255])).

tff(c_5988,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5966,c_2917])).

tff(c_6037,plain,
    ( k1_xboole_0 = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_5988])).

tff(c_6039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1193,c_1137,c_6037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:14:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.28  
% 6.10/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.10/2.29  
% 6.10/2.29  %Foreground sorts:
% 6.10/2.29  
% 6.10/2.29  
% 6.10/2.29  %Background operators:
% 6.10/2.29  
% 6.10/2.29  
% 6.10/2.29  %Foreground operators:
% 6.10/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.10/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.10/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.10/2.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.10/2.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.10/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.10/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.10/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.10/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.10/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.10/2.29  tff('#skF_3', type, '#skF_3': $i).
% 6.10/2.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.10/2.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.10/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.10/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.10/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.10/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.10/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.10/2.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.10/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.10/2.29  
% 6.10/2.30  tff(f_140, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.10/2.30  tff(f_78, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.10/2.30  tff(f_113, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.10/2.30  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.10/2.30  tff(f_76, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 6.10/2.30  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.10/2.30  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.10/2.30  tff(f_107, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.10/2.30  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.10/2.30  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.10/2.30  tff(f_121, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.10/2.30  tff(f_82, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.10/2.30  tff(f_42, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.10/2.30  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.10/2.30  tff(f_84, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.10/2.30  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.10/2.30  tff(f_80, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.10/2.30  tff(c_74, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.10/2.30  tff(c_116, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_74])).
% 6.10/2.30  tff(c_72, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.10/2.30  tff(c_105, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_72])).
% 6.10/2.30  tff(c_78, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.10/2.30  tff(c_127, plain, (![A_86, B_87]: (r1_tarski(A_86, k2_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.10/2.30  tff(c_130, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_127])).
% 6.10/2.30  tff(c_434, plain, (![B_142, A_143]: (k1_tarski(B_142)=A_143 | k1_xboole_0=A_143 | ~r1_tarski(A_143, k1_tarski(B_142)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.10/2.30  tff(c_437, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_130, c_434])).
% 6.10/2.30  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_105, c_437])).
% 6.10/2.30  tff(c_449, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_74])).
% 6.10/2.30  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.10/2.30  tff(c_450, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_74])).
% 6.10/2.30  tff(c_26, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.10/2.30  tff(c_454, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_450, c_26])).
% 6.10/2.30  tff(c_804, plain, (![A_207, B_208, C_209]: (~r1_xboole_0(A_207, B_208) | ~r2_hidden(C_209, B_208) | ~r2_hidden(C_209, A_207))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.10/2.30  tff(c_814, plain, (![C_210]: (~r2_hidden(C_210, '#skF_4'))), inference(resolution, [status(thm)], [c_454, c_804])).
% 6.10/2.30  tff(c_859, plain, (![B_214]: (r1_tarski('#skF_4', B_214))), inference(resolution, [status(thm)], [c_8, c_814])).
% 6.10/2.30  tff(c_24, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.10/2.30  tff(c_869, plain, (![B_214]: (k2_xboole_0('#skF_4', B_214)=B_214)), inference(resolution, [status(thm)], [c_859, c_24])).
% 6.10/2.30  tff(c_1134, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_869, c_78])).
% 6.10/2.30  tff(c_1136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_449, c_1134])).
% 6.10/2.30  tff(c_1138, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_72])).
% 6.10/2.30  tff(c_76, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.10/2.30  tff(c_1193, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_1138, c_76])).
% 6.10/2.30  tff(c_1137, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_72])).
% 6.10/2.30  tff(c_1143, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_78])).
% 6.10/2.30  tff(c_56, plain, (![A_70, B_71]: (r1_xboole_0(k1_tarski(A_70), B_71) | r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.10/2.30  tff(c_1325, plain, (![A_245, B_246]: (k3_xboole_0(A_245, B_246)=k1_xboole_0 | ~r1_xboole_0(A_245, B_246))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.30  tff(c_1509, plain, (![A_281, B_282]: (k3_xboole_0(k1_tarski(A_281), B_282)=k1_xboole_0 | r2_hidden(A_281, B_282))), inference(resolution, [status(thm)], [c_56, c_1325])).
% 6.10/2.30  tff(c_1522, plain, (![B_282]: (k3_xboole_0('#skF_4', B_282)=k1_xboole_0 | r2_hidden('#skF_3', B_282))), inference(superposition, [status(thm), theory('equality')], [c_1138, c_1509])).
% 6.10/2.30  tff(c_42, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.10/2.30  tff(c_3047, plain, (![A_340, B_341, C_342]: (r1_tarski(k2_tarski(A_340, B_341), C_342) | ~r2_hidden(B_341, C_342) | ~r2_hidden(A_340, C_342))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.10/2.30  tff(c_4868, plain, (![A_455, C_456]: (r1_tarski(k1_tarski(A_455), C_456) | ~r2_hidden(A_455, C_456) | ~r2_hidden(A_455, C_456))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3047])).
% 6.10/2.30  tff(c_4896, plain, (![A_457, C_458]: (k2_xboole_0(k1_tarski(A_457), C_458)=C_458 | ~r2_hidden(A_457, C_458))), inference(resolution, [status(thm)], [c_4868, c_24])).
% 6.10/2.30  tff(c_5163, plain, (![C_464]: (k2_xboole_0('#skF_4', C_464)=C_464 | ~r2_hidden('#skF_3', C_464))), inference(superposition, [status(thm), theory('equality')], [c_1138, c_4896])).
% 6.10/2.30  tff(c_5966, plain, (![B_486]: (k2_xboole_0('#skF_4', B_486)=B_486 | k3_xboole_0('#skF_4', B_486)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1522, c_5163])).
% 6.10/2.30  tff(c_34, plain, (![A_27]: (k5_xboole_0(A_27, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.30  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.10/2.30  tff(c_14, plain, (![A_10]: (k2_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.10/2.30  tff(c_2185, plain, (![A_322, B_323]: (k5_xboole_0(k5_xboole_0(A_322, B_323), k2_xboole_0(A_322, B_323))=k3_xboole_0(A_322, B_323))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.10/2.30  tff(c_2258, plain, (![A_10]: (k5_xboole_0(k5_xboole_0(A_10, A_10), A_10)=k3_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2185])).
% 6.10/2.30  tff(c_2270, plain, (![A_324]: (k5_xboole_0(k1_xboole_0, A_324)=A_324)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16, c_2258])).
% 6.10/2.30  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.10/2.30  tff(c_2301, plain, (![A_324]: (k5_xboole_0(A_324, k1_xboole_0)=A_324)), inference(superposition, [status(thm), theory('equality')], [c_2270, c_2])).
% 6.10/2.30  tff(c_1868, plain, (![A_311, B_312, C_313]: (k5_xboole_0(k5_xboole_0(A_311, B_312), C_313)=k5_xboole_0(A_311, k5_xboole_0(B_312, C_313)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.10/2.30  tff(c_1884, plain, (![A_311, B_312]: (k5_xboole_0(A_311, k5_xboole_0(B_312, k5_xboole_0(A_311, B_312)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1868, c_34])).
% 6.10/2.30  tff(c_2265, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16, c_2258])).
% 6.10/2.30  tff(c_1907, plain, (![A_27, C_313]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_313))=k5_xboole_0(k1_xboole_0, C_313))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1868])).
% 6.10/2.30  tff(c_2453, plain, (![A_326, C_327]: (k5_xboole_0(A_326, k5_xboole_0(A_326, C_327))=C_327)), inference(demodulation, [status(thm), theory('equality')], [c_2265, c_1907])).
% 6.10/2.30  tff(c_2509, plain, (![B_312, A_311]: (k5_xboole_0(B_312, k5_xboole_0(A_311, B_312))=k5_xboole_0(A_311, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1884, c_2453])).
% 6.10/2.30  tff(c_2543, plain, (![B_312, A_311]: (k5_xboole_0(B_312, k5_xboole_0(A_311, B_312))=A_311)), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_2509])).
% 6.10/2.30  tff(c_2549, plain, (![B_328, A_329]: (k5_xboole_0(B_328, k5_xboole_0(A_329, B_328))=A_329)), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_2509])).
% 6.10/2.30  tff(c_2579, plain, (![A_311, B_312]: (k5_xboole_0(k5_xboole_0(A_311, B_312), A_311)=B_312)), inference(superposition, [status(thm), theory('equality')], [c_2543, c_2549])).
% 6.10/2.30  tff(c_2255, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1143, c_2185])).
% 6.10/2.30  tff(c_2917, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_2255])).
% 6.10/2.30  tff(c_5988, plain, (k1_xboole_0='#skF_5' | k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5966, c_2917])).
% 6.10/2.30  tff(c_6037, plain, (k1_xboole_0='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_5988])).
% 6.10/2.30  tff(c_6039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1193, c_1137, c_6037])).
% 6.10/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.30  
% 6.10/2.30  Inference rules
% 6.10/2.30  ----------------------
% 6.10/2.30  #Ref     : 0
% 6.10/2.30  #Sup     : 1424
% 6.10/2.30  #Fact    : 0
% 6.10/2.30  #Define  : 0
% 6.10/2.30  #Split   : 3
% 6.10/2.30  #Chain   : 0
% 6.10/2.30  #Close   : 0
% 6.10/2.30  
% 6.10/2.30  Ordering : KBO
% 6.10/2.30  
% 6.10/2.30  Simplification rules
% 6.10/2.30  ----------------------
% 6.10/2.30  #Subsume      : 85
% 6.10/2.30  #Demod        : 1096
% 6.10/2.30  #Tautology    : 841
% 6.10/2.30  #SimpNegUnit  : 19
% 6.10/2.30  #BackRed      : 13
% 6.10/2.30  
% 6.10/2.30  #Partial instantiations: 0
% 6.10/2.30  #Strategies tried      : 1
% 6.10/2.30  
% 6.10/2.30  Timing (in seconds)
% 6.10/2.30  ----------------------
% 6.45/2.31  Preprocessing        : 0.37
% 6.45/2.31  Parsing              : 0.19
% 6.45/2.31  CNF conversion       : 0.03
% 6.45/2.31  Main loop            : 1.14
% 6.45/2.31  Inferencing          : 0.37
% 6.45/2.31  Reduction            : 0.48
% 6.45/2.31  Demodulation         : 0.39
% 6.45/2.31  BG Simplification    : 0.04
% 6.45/2.31  Subsumption          : 0.17
% 6.45/2.31  Abstraction          : 0.05
% 6.45/2.31  MUC search           : 0.00
% 6.45/2.31  Cooper               : 0.00
% 6.45/2.31  Total                : 1.56
% 6.45/2.31  Index Insertion      : 0.00
% 6.45/2.31  Index Deletion       : 0.00
% 6.45/2.31  Index Matching       : 0.00
% 6.45/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
