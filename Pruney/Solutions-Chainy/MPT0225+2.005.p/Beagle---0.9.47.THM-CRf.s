%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:31 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 780 expanded)
%              Number of leaves         :   33 ( 263 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 (1049 expanded)
%              Number of equality atoms :   61 ( 831 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_88,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_28,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3718,plain,(
    ! [A_3146,B_3147] :
      ( k3_xboole_0(A_3146,B_3147) = A_3146
      | ~ r1_tarski(A_3146,B_3147) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3740,plain,(
    ! [A_3149] : k3_xboole_0(k1_xboole_0,A_3149) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_3718])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3749,plain,(
    ! [A_3149] : k3_xboole_0(A_3149,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3740,c_2])).

tff(c_30,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3975,plain,(
    ! [A_3168,B_3169] : k4_xboole_0(A_3168,k4_xboole_0(A_3168,B_3169)) = k3_xboole_0(A_3168,B_3169) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4007,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3975])).

tff(c_4014,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3749,c_4007])).

tff(c_2280,plain,(
    ! [A_176,B_177] :
      ( k3_xboole_0(A_176,B_177) = A_176
      | ~ r1_tarski(A_176,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2307,plain,(
    ! [A_181] : k3_xboole_0(k1_xboole_0,A_181) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_2280])).

tff(c_2316,plain,(
    ! [A_181] : k3_xboole_0(A_181,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2307,c_2])).

tff(c_2559,plain,(
    ! [A_194,B_195] : k4_xboole_0(A_194,k4_xboole_0(A_194,B_195)) = k3_xboole_0(A_194,B_195) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2594,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2559])).

tff(c_2602,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2316,c_2594])).

tff(c_70,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_97,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_281,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = A_70
      | ~ r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2076,plain,(
    ! [A_162,B_163] :
      ( k4_xboole_0(k1_tarski(A_162),B_163) = k1_tarski(A_162)
      | r2_hidden(A_162,B_163) ) ),
    inference(resolution,[status(thm)],[c_64,c_281])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_107,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_2186,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2076,c_107])).

tff(c_44,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2195,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2186,c_44])).

tff(c_2199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_2195])).

tff(c_2201,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2200,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2382,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2200,c_2200,c_72])).

tff(c_2383,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2382])).

tff(c_2422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2201,c_2383])).

tff(c_2423,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2382])).

tff(c_2609,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2602,c_2423])).

tff(c_3246,plain,(
    ! [B_225,A_226] :
      ( r2_hidden(B_225,A_226)
      | k3_xboole_0(A_226,k1_tarski(B_225)) != k1_tarski(B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3252,plain,(
    ! [A_226] :
      ( r2_hidden('#skF_6',A_226)
      | k3_xboole_0(A_226,k1_xboole_0) != k1_tarski('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2609,c_3246])).

tff(c_3274,plain,(
    ! [A_227] : r2_hidden('#skF_6',A_227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2609,c_2316,c_3252])).

tff(c_3287,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3274,c_44])).

tff(c_3285,plain,(
    ! [A_25] : A_25 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3274,c_44])).

tff(c_3453,plain,(
    ! [A_1675] : A_1675 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3287,c_3285])).

tff(c_3617,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3453,c_97])).

tff(c_3618,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_3619,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3620,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_3630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3619,c_3620])).

tff(c_3631,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_3710,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3618,c_3618,c_3631])).

tff(c_4016,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_3710])).

tff(c_4594,plain,(
    ! [B_3198,A_3199] :
      ( r2_hidden(B_3198,A_3199)
      | k3_xboole_0(A_3199,k1_tarski(B_3198)) != k1_tarski(B_3198) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4597,plain,(
    ! [A_3199] :
      ( r2_hidden('#skF_6',A_3199)
      | k3_xboole_0(A_3199,k1_xboole_0) != k1_tarski('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4016,c_4594])).

tff(c_4619,plain,(
    ! [A_3200] : r2_hidden('#skF_6',A_3200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4016,c_3749,c_4597])).

tff(c_4635,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4619,c_44])).

tff(c_4630,plain,(
    ! [A_25] : A_25 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4619,c_44])).

tff(c_4920,plain,(
    ! [A_5822] : A_5822 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4635,c_4630])).

tff(c_4615,plain,(
    ! [A_3199] : r2_hidden('#skF_6',A_3199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4016,c_3749,c_4597])).

tff(c_4929,plain,(
    ! [A_3199] : r2_hidden('#skF_3',A_3199) ),
    inference(superposition,[status(thm),theory(equality)],[c_4920,c_4615])).

tff(c_5451,plain,(
    ! [A_9095,C_9096,B_9097] :
      ( ~ r2_hidden(A_9095,C_9096)
      | ~ r2_hidden(A_9095,B_9097)
      | ~ r2_hidden(A_9095,k5_xboole_0(B_9097,C_9096)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5458,plain,(
    ! [C_9096,B_9097] :
      ( ~ r2_hidden('#skF_3',C_9096)
      | ~ r2_hidden('#skF_3',B_9097) ) ),
    inference(resolution,[status(thm)],[c_4929,c_5451])).

tff(c_5498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_4929,c_5458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.01  
% 5.12/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.01  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.12/2.01  
% 5.12/2.01  %Foreground sorts:
% 5.12/2.01  
% 5.12/2.01  
% 5.12/2.01  %Background operators:
% 5.12/2.01  
% 5.12/2.01  
% 5.12/2.01  %Foreground operators:
% 5.12/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.12/2.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.12/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.12/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.12/2.01  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.12/2.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.12/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.12/2.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.12/2.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.12/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.12/2.01  tff('#skF_6', type, '#skF_6': $i).
% 5.12/2.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.12/2.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.12/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.12/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.12/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/2.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.12/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.12/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.12/2.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.12/2.01  
% 5.12/2.02  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.12/2.02  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.12/2.02  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.12/2.02  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.12/2.02  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.12/2.02  tff(f_94, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 5.12/2.02  tff(f_84, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.12/2.02  tff(f_62, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.12/2.02  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.12/2.02  tff(f_88, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 5.12/2.02  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.12/2.02  tff(c_28, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.12/2.02  tff(c_3718, plain, (![A_3146, B_3147]: (k3_xboole_0(A_3146, B_3147)=A_3146 | ~r1_tarski(A_3146, B_3147))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.12/2.02  tff(c_3740, plain, (![A_3149]: (k3_xboole_0(k1_xboole_0, A_3149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_3718])).
% 5.12/2.02  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/2.02  tff(c_3749, plain, (![A_3149]: (k3_xboole_0(A_3149, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3740, c_2])).
% 5.12/2.02  tff(c_30, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.12/2.02  tff(c_3975, plain, (![A_3168, B_3169]: (k4_xboole_0(A_3168, k4_xboole_0(A_3168, B_3169))=k3_xboole_0(A_3168, B_3169))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.12/2.02  tff(c_4007, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3975])).
% 5.12/2.02  tff(c_4014, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3749, c_4007])).
% 5.12/2.02  tff(c_2280, plain, (![A_176, B_177]: (k3_xboole_0(A_176, B_177)=A_176 | ~r1_tarski(A_176, B_177))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.12/2.02  tff(c_2307, plain, (![A_181]: (k3_xboole_0(k1_xboole_0, A_181)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_2280])).
% 5.12/2.02  tff(c_2316, plain, (![A_181]: (k3_xboole_0(A_181, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2307, c_2])).
% 5.12/2.02  tff(c_2559, plain, (![A_194, B_195]: (k4_xboole_0(A_194, k4_xboole_0(A_194, B_195))=k3_xboole_0(A_194, B_195))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.12/2.02  tff(c_2594, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2559])).
% 5.12/2.02  tff(c_2602, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2316, c_2594])).
% 5.12/2.02  tff(c_70, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.12/2.02  tff(c_97, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_70])).
% 5.12/2.02  tff(c_64, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.12/2.02  tff(c_281, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=A_70 | ~r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.12/2.02  tff(c_2076, plain, (![A_162, B_163]: (k4_xboole_0(k1_tarski(A_162), B_163)=k1_tarski(A_162) | r2_hidden(A_162, B_163))), inference(resolution, [status(thm)], [c_64, c_281])).
% 5.12/2.02  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.12/2.02  tff(c_107, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 5.12/2.02  tff(c_2186, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2076, c_107])).
% 5.12/2.02  tff(c_44, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.12/2.02  tff(c_2195, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2186, c_44])).
% 5.12/2.02  tff(c_2199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_2195])).
% 5.12/2.02  tff(c_2201, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 5.12/2.02  tff(c_2200, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_68])).
% 5.12/2.02  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.12/2.02  tff(c_2382, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2200, c_2200, c_72])).
% 5.12/2.02  tff(c_2383, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_2382])).
% 5.12/2.02  tff(c_2422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2201, c_2383])).
% 5.12/2.02  tff(c_2423, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_2382])).
% 5.12/2.02  tff(c_2609, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2602, c_2423])).
% 5.12/2.02  tff(c_3246, plain, (![B_225, A_226]: (r2_hidden(B_225, A_226) | k3_xboole_0(A_226, k1_tarski(B_225))!=k1_tarski(B_225))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.12/2.02  tff(c_3252, plain, (![A_226]: (r2_hidden('#skF_6', A_226) | k3_xboole_0(A_226, k1_xboole_0)!=k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2609, c_3246])).
% 5.12/2.02  tff(c_3274, plain, (![A_227]: (r2_hidden('#skF_6', A_227))), inference(demodulation, [status(thm), theory('equality')], [c_2609, c_2316, c_3252])).
% 5.12/2.02  tff(c_3287, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_3274, c_44])).
% 5.12/2.02  tff(c_3285, plain, (![A_25]: (A_25='#skF_6')), inference(resolution, [status(thm)], [c_3274, c_44])).
% 5.12/2.02  tff(c_3453, plain, (![A_1675]: (A_1675='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3287, c_3285])).
% 5.12/2.02  tff(c_3617, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3453, c_97])).
% 5.12/2.02  tff(c_3618, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_70])).
% 5.12/2.02  tff(c_3619, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 5.12/2.02  tff(c_74, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.12/2.02  tff(c_3620, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_74])).
% 5.12/2.02  tff(c_3630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3619, c_3620])).
% 5.12/2.02  tff(c_3631, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 5.12/2.02  tff(c_3710, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3618, c_3618, c_3631])).
% 5.12/2.02  tff(c_4016, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_3710])).
% 5.12/2.02  tff(c_4594, plain, (![B_3198, A_3199]: (r2_hidden(B_3198, A_3199) | k3_xboole_0(A_3199, k1_tarski(B_3198))!=k1_tarski(B_3198))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.12/2.02  tff(c_4597, plain, (![A_3199]: (r2_hidden('#skF_6', A_3199) | k3_xboole_0(A_3199, k1_xboole_0)!=k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4016, c_4594])).
% 5.12/2.02  tff(c_4619, plain, (![A_3200]: (r2_hidden('#skF_6', A_3200))), inference(demodulation, [status(thm), theory('equality')], [c_4016, c_3749, c_4597])).
% 5.12/2.02  tff(c_4635, plain, ('#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_4619, c_44])).
% 5.12/2.02  tff(c_4630, plain, (![A_25]: (A_25='#skF_6')), inference(resolution, [status(thm)], [c_4619, c_44])).
% 5.12/2.02  tff(c_4920, plain, (![A_5822]: (A_5822='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4635, c_4630])).
% 5.12/2.02  tff(c_4615, plain, (![A_3199]: (r2_hidden('#skF_6', A_3199))), inference(demodulation, [status(thm), theory('equality')], [c_4016, c_3749, c_4597])).
% 5.12/2.02  tff(c_4929, plain, (![A_3199]: (r2_hidden('#skF_3', A_3199))), inference(superposition, [status(thm), theory('equality')], [c_4920, c_4615])).
% 5.12/2.02  tff(c_5451, plain, (![A_9095, C_9096, B_9097]: (~r2_hidden(A_9095, C_9096) | ~r2_hidden(A_9095, B_9097) | ~r2_hidden(A_9095, k5_xboole_0(B_9097, C_9096)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.12/2.02  tff(c_5458, plain, (![C_9096, B_9097]: (~r2_hidden('#skF_3', C_9096) | ~r2_hidden('#skF_3', B_9097))), inference(resolution, [status(thm)], [c_4929, c_5451])).
% 5.12/2.02  tff(c_5498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4929, c_4929, c_5458])).
% 5.12/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.02  
% 5.12/2.02  Inference rules
% 5.12/2.02  ----------------------
% 5.12/2.02  #Ref     : 0
% 5.12/2.02  #Sup     : 1494
% 5.12/2.02  #Fact    : 0
% 5.12/2.02  #Define  : 0
% 5.12/2.02  #Split   : 4
% 5.12/2.02  #Chain   : 0
% 5.12/2.02  #Close   : 0
% 5.12/2.02  
% 5.12/2.02  Ordering : KBO
% 5.12/2.02  
% 5.12/2.02  Simplification rules
% 5.12/2.02  ----------------------
% 5.12/2.02  #Subsume      : 178
% 5.12/2.02  #Demod        : 842
% 5.12/2.02  #Tautology    : 862
% 5.12/2.02  #SimpNegUnit  : 1
% 5.12/2.02  #BackRed      : 8
% 5.12/2.02  
% 5.12/2.02  #Partial instantiations: 327
% 5.12/2.02  #Strategies tried      : 1
% 5.12/2.02  
% 5.12/2.02  Timing (in seconds)
% 5.12/2.02  ----------------------
% 5.12/2.03  Preprocessing        : 0.32
% 5.12/2.03  Parsing              : 0.17
% 5.12/2.03  CNF conversion       : 0.02
% 5.12/2.03  Main loop            : 0.88
% 5.12/2.03  Inferencing          : 0.34
% 5.12/2.03  Reduction            : 0.31
% 5.12/2.03  Demodulation         : 0.25
% 5.12/2.03  BG Simplification    : 0.03
% 5.12/2.03  Subsumption          : 0.11
% 5.12/2.03  Abstraction          : 0.04
% 5.12/2.03  MUC search           : 0.00
% 5.12/2.03  Cooper               : 0.00
% 5.12/2.03  Total                : 1.23
% 5.12/2.03  Index Insertion      : 0.00
% 5.12/2.03  Index Deletion       : 0.00
% 5.12/2.03  Index Matching       : 0.00
% 5.12/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
