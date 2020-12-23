%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:05 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 223 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 438 expanded)
%              Number of equality atoms :   55 ( 169 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_56,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_30,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_178,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_301,plain,(
    ! [D_83,A_84,B_85] :
      ( r2_hidden(D_83,k4_xboole_0(A_84,B_85))
      | r2_hidden(D_83,B_85)
      | ~ r2_hidden(D_83,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_319,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k1_xboole_0)
      | r2_hidden(D_86,'#skF_8')
      | ~ r2_hidden(D_86,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_301])).

tff(c_326,plain,
    ( r2_hidden('#skF_7',k1_xboole_0)
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_319])).

tff(c_330,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_326])).

tff(c_26,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_195,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_212,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_195])).

tff(c_215,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_212])).

tff(c_245,plain,(
    ! [D_61,B_62,A_63] :
      ( ~ r2_hidden(D_61,B_62)
      | ~ r2_hidden(D_61,k4_xboole_0(A_63,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_251,plain,(
    ! [D_61,A_11] :
      ( ~ r2_hidden(D_61,k1_xboole_0)
      | ~ r2_hidden(D_61,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_245])).

tff(c_338,plain,(
    ! [A_11] : ~ r2_hidden('#skF_7',A_11) ),
    inference(resolution,[status(thm)],[c_330,c_251])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_330])).

tff(c_341,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1770,plain,(
    ! [A_3253,B_3254,C_3255] :
      ( r2_hidden('#skF_1'(A_3253,B_3254,C_3255),A_3253)
      | r2_hidden('#skF_2'(A_3253,B_3254,C_3255),C_3255)
      | k4_xboole_0(A_3253,B_3254) = C_3255 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1840,plain,(
    ! [A_3253,C_3255] :
      ( r2_hidden('#skF_2'(A_3253,A_3253,C_3255),C_3255)
      | k4_xboole_0(A_3253,A_3253) = C_3255 ) ),
    inference(resolution,[status(thm)],[c_1770,c_18])).

tff(c_1859,plain,(
    ! [A_3308,C_3309] :
      ( r2_hidden('#skF_2'(A_3308,A_3308,C_3309),C_3309)
      | k4_xboole_0(A_3308,A_3308) = C_3309 ) ),
    inference(resolution,[status(thm)],[c_1770,c_18])).

tff(c_357,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_374,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_357])).

tff(c_387,plain,(
    ! [A_100] : k4_xboole_0(A_100,k1_xboole_0) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_374])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_396,plain,(
    ! [D_8,A_100] :
      ( ~ r2_hidden(D_8,k1_xboole_0)
      | ~ r2_hidden(D_8,A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_6])).

tff(c_1959,plain,(
    ! [A_3475,A_3476] :
      ( ~ r2_hidden('#skF_2'(A_3475,A_3475,k1_xboole_0),A_3476)
      | k4_xboole_0(A_3475,A_3475) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1859,c_396])).

tff(c_2000,plain,(
    ! [A_3253] : k4_xboole_0(A_3253,A_3253) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1840,c_1959])).

tff(c_2076,plain,(
    ! [A_3688,C_3689] :
      ( r2_hidden('#skF_2'(A_3688,A_3688,C_3689),C_3689)
      | k1_xboole_0 = C_3689 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_1840])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2973,plain,(
    ! [A_5078,A_5079,B_5080] :
      ( r2_hidden('#skF_2'(A_5078,A_5078,k4_xboole_0(A_5079,B_5080)),A_5079)
      | k4_xboole_0(A_5079,B_5080) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2076,c_8])).

tff(c_28,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3240,plain,(
    ! [A_5187,A_5188,B_5189] :
      ( '#skF_2'(A_5187,A_5187,k4_xboole_0(k1_tarski(A_5188),B_5189)) = A_5188
      | k4_xboole_0(k1_tarski(A_5188),B_5189) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2973,c_28])).

tff(c_2125,plain,(
    ! [A_3688,A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3688,A_3688,k4_xboole_0(A_3,B_4)),B_4)
      | k4_xboole_0(A_3,B_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2076,c_6])).

tff(c_3252,plain,(
    ! [A_5188,B_5189] :
      ( ~ r2_hidden(A_5188,B_5189)
      | k4_xboole_0(k1_tarski(A_5188),B_5189) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_5188),B_5189) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3240,c_2125])).

tff(c_3898,plain,(
    ! [A_5563,B_5564] :
      ( ~ r2_hidden(A_5563,B_5564)
      | k4_xboole_0(k1_tarski(A_5563),B_5564) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3252])).

tff(c_342,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_428,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_58])).

tff(c_3931,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3898,c_428])).

tff(c_4025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_3931])).

tff(c_4026,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5533,plain,(
    ! [A_8511,B_8512,C_8513] :
      ( ~ r2_hidden('#skF_1'(A_8511,B_8512,C_8513),B_8512)
      | r2_hidden('#skF_2'(A_8511,B_8512,C_8513),C_8513)
      | k4_xboole_0(A_8511,B_8512) = C_8513 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5556,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_5533])).

tff(c_5563,plain,(
    ! [A_8566,C_8567] :
      ( r2_hidden('#skF_2'(A_8566,A_8566,C_8567),C_8567)
      | k4_xboole_0(A_8566,A_8566) = C_8567 ) ),
    inference(resolution,[status(thm)],[c_20,c_5533])).

tff(c_4126,plain,(
    ! [A_5622,B_5623] : k5_xboole_0(A_5622,k3_xboole_0(A_5622,B_5623)) = k4_xboole_0(A_5622,B_5623) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4143,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4126])).

tff(c_4146,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4143])).

tff(c_4184,plain,(
    ! [D_5629,B_5630,A_5631] :
      ( ~ r2_hidden(D_5629,B_5630)
      | ~ r2_hidden(D_5629,k4_xboole_0(A_5631,B_5630)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4190,plain,(
    ! [D_5629,A_11] :
      ( ~ r2_hidden(D_5629,k1_xboole_0)
      | ~ r2_hidden(D_5629,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4146,c_4184])).

tff(c_5607,plain,(
    ! [A_8620,A_8621] :
      ( ~ r2_hidden('#skF_2'(A_8620,A_8620,k1_xboole_0),A_8621)
      | k4_xboole_0(A_8620,A_8620) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5563,c_4190])).

tff(c_5642,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5556,c_5607])).

tff(c_5708,plain,(
    ! [A_8833,C_8834] :
      ( r2_hidden('#skF_2'(A_8833,A_8833,C_8834),C_8834)
      | k1_xboole_0 = C_8834 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5642,c_5556])).

tff(c_6210,plain,(
    ! [A_9484,A_9485,B_9486] :
      ( r2_hidden('#skF_2'(A_9484,A_9484,k4_xboole_0(A_9485,B_9486)),A_9485)
      | k4_xboole_0(A_9485,B_9486) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5708,c_8])).

tff(c_6501,plain,(
    ! [A_9648,A_9649,B_9650] :
      ( '#skF_2'(A_9648,A_9648,k4_xboole_0(k1_tarski(A_9649),B_9650)) = A_9649
      | k4_xboole_0(k1_tarski(A_9649),B_9650) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6210,c_28])).

tff(c_5756,plain,(
    ! [A_8833,A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_8833,A_8833,k4_xboole_0(A_3,B_4)),B_4)
      | k4_xboole_0(A_3,B_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5708,c_6])).

tff(c_6513,plain,(
    ! [A_9649,B_9650] :
      ( ~ r2_hidden(A_9649,B_9650)
      | k4_xboole_0(k1_tarski(A_9649),B_9650) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_9649),B_9650) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6501,c_5756])).

tff(c_7105,plain,(
    ! [A_9917,B_9918] :
      ( ~ r2_hidden(A_9917,B_9918)
      | k4_xboole_0(k1_tarski(A_9917),B_9918) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6513])).

tff(c_4027,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4115,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4027,c_54])).

tff(c_7144,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7105,c_4115])).

tff(c_7224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4026,c_7144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.54/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.08  
% 5.54/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.08  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 5.54/2.08  
% 5.54/2.08  %Foreground sorts:
% 5.54/2.08  
% 5.54/2.08  
% 5.54/2.08  %Background operators:
% 5.54/2.08  
% 5.54/2.08  
% 5.54/2.08  %Foreground operators:
% 5.54/2.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.54/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.54/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.54/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.54/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.54/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.54/2.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.54/2.08  tff('#skF_7', type, '#skF_7': $i).
% 5.54/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.54/2.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.54/2.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.54/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.54/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.54/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.54/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.54/2.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.54/2.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.54/2.08  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.54/2.08  tff('#skF_8', type, '#skF_8': $i).
% 5.54/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.54/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.54/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.54/2.08  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.54/2.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.54/2.08  
% 5.54/2.10  tff(f_69, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 5.54/2.10  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.54/2.10  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.54/2.10  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.54/2.10  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.54/2.10  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.54/2.10  tff(c_56, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.54/2.10  tff(c_93, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_56])).
% 5.54/2.10  tff(c_30, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.54/2.10  tff(c_60, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.54/2.10  tff(c_178, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 5.54/2.10  tff(c_301, plain, (![D_83, A_84, B_85]: (r2_hidden(D_83, k4_xboole_0(A_84, B_85)) | r2_hidden(D_83, B_85) | ~r2_hidden(D_83, A_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_319, plain, (![D_86]: (r2_hidden(D_86, k1_xboole_0) | r2_hidden(D_86, '#skF_8') | ~r2_hidden(D_86, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_178, c_301])).
% 5.54/2.10  tff(c_326, plain, (r2_hidden('#skF_7', k1_xboole_0) | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_30, c_319])).
% 5.54/2.10  tff(c_330, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_93, c_326])).
% 5.54/2.10  tff(c_26, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.54/2.10  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.54/2.10  tff(c_195, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.54/2.10  tff(c_212, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_195])).
% 5.54/2.10  tff(c_215, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_212])).
% 5.54/2.10  tff(c_245, plain, (![D_61, B_62, A_63]: (~r2_hidden(D_61, B_62) | ~r2_hidden(D_61, k4_xboole_0(A_63, B_62)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_251, plain, (![D_61, A_11]: (~r2_hidden(D_61, k1_xboole_0) | ~r2_hidden(D_61, A_11))), inference(superposition, [status(thm), theory('equality')], [c_215, c_245])).
% 5.54/2.10  tff(c_338, plain, (![A_11]: (~r2_hidden('#skF_7', A_11))), inference(resolution, [status(thm)], [c_330, c_251])).
% 5.54/2.10  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_330])).
% 5.54/2.10  tff(c_341, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 5.54/2.10  tff(c_1770, plain, (![A_3253, B_3254, C_3255]: (r2_hidden('#skF_1'(A_3253, B_3254, C_3255), A_3253) | r2_hidden('#skF_2'(A_3253, B_3254, C_3255), C_3255) | k4_xboole_0(A_3253, B_3254)=C_3255)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_1840, plain, (![A_3253, C_3255]: (r2_hidden('#skF_2'(A_3253, A_3253, C_3255), C_3255) | k4_xboole_0(A_3253, A_3253)=C_3255)), inference(resolution, [status(thm)], [c_1770, c_18])).
% 5.54/2.10  tff(c_1859, plain, (![A_3308, C_3309]: (r2_hidden('#skF_2'(A_3308, A_3308, C_3309), C_3309) | k4_xboole_0(A_3308, A_3308)=C_3309)), inference(resolution, [status(thm)], [c_1770, c_18])).
% 5.54/2.10  tff(c_357, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.54/2.10  tff(c_374, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_357])).
% 5.54/2.10  tff(c_387, plain, (![A_100]: (k4_xboole_0(A_100, k1_xboole_0)=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_374])).
% 5.54/2.10  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_396, plain, (![D_8, A_100]: (~r2_hidden(D_8, k1_xboole_0) | ~r2_hidden(D_8, A_100))), inference(superposition, [status(thm), theory('equality')], [c_387, c_6])).
% 5.54/2.10  tff(c_1959, plain, (![A_3475, A_3476]: (~r2_hidden('#skF_2'(A_3475, A_3475, k1_xboole_0), A_3476) | k4_xboole_0(A_3475, A_3475)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1859, c_396])).
% 5.54/2.10  tff(c_2000, plain, (![A_3253]: (k4_xboole_0(A_3253, A_3253)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1840, c_1959])).
% 5.54/2.10  tff(c_2076, plain, (![A_3688, C_3689]: (r2_hidden('#skF_2'(A_3688, A_3688, C_3689), C_3689) | k1_xboole_0=C_3689)), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_1840])).
% 5.54/2.10  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_2973, plain, (![A_5078, A_5079, B_5080]: (r2_hidden('#skF_2'(A_5078, A_5078, k4_xboole_0(A_5079, B_5080)), A_5079) | k4_xboole_0(A_5079, B_5080)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2076, c_8])).
% 5.54/2.10  tff(c_28, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.54/2.10  tff(c_3240, plain, (![A_5187, A_5188, B_5189]: ('#skF_2'(A_5187, A_5187, k4_xboole_0(k1_tarski(A_5188), B_5189))=A_5188 | k4_xboole_0(k1_tarski(A_5188), B_5189)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2973, c_28])).
% 5.54/2.10  tff(c_2125, plain, (![A_3688, A_3, B_4]: (~r2_hidden('#skF_2'(A_3688, A_3688, k4_xboole_0(A_3, B_4)), B_4) | k4_xboole_0(A_3, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2076, c_6])).
% 5.54/2.10  tff(c_3252, plain, (![A_5188, B_5189]: (~r2_hidden(A_5188, B_5189) | k4_xboole_0(k1_tarski(A_5188), B_5189)=k1_xboole_0 | k4_xboole_0(k1_tarski(A_5188), B_5189)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3240, c_2125])).
% 5.54/2.10  tff(c_3898, plain, (![A_5563, B_5564]: (~r2_hidden(A_5563, B_5564) | k4_xboole_0(k1_tarski(A_5563), B_5564)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_3252])).
% 5.54/2.10  tff(c_342, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 5.54/2.10  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.54/2.10  tff(c_428, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_342, c_58])).
% 5.54/2.10  tff(c_3931, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3898, c_428])).
% 5.54/2.10  tff(c_4025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_3931])).
% 5.54/2.10  tff(c_4026, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 5.54/2.10  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_5533, plain, (![A_8511, B_8512, C_8513]: (~r2_hidden('#skF_1'(A_8511, B_8512, C_8513), B_8512) | r2_hidden('#skF_2'(A_8511, B_8512, C_8513), C_8513) | k4_xboole_0(A_8511, B_8512)=C_8513)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_5556, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_5533])).
% 5.54/2.10  tff(c_5563, plain, (![A_8566, C_8567]: (r2_hidden('#skF_2'(A_8566, A_8566, C_8567), C_8567) | k4_xboole_0(A_8566, A_8566)=C_8567)), inference(resolution, [status(thm)], [c_20, c_5533])).
% 5.54/2.10  tff(c_4126, plain, (![A_5622, B_5623]: (k5_xboole_0(A_5622, k3_xboole_0(A_5622, B_5623))=k4_xboole_0(A_5622, B_5623))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.54/2.10  tff(c_4143, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4126])).
% 5.54/2.10  tff(c_4146, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4143])).
% 5.54/2.10  tff(c_4184, plain, (![D_5629, B_5630, A_5631]: (~r2_hidden(D_5629, B_5630) | ~r2_hidden(D_5629, k4_xboole_0(A_5631, B_5630)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.10  tff(c_4190, plain, (![D_5629, A_11]: (~r2_hidden(D_5629, k1_xboole_0) | ~r2_hidden(D_5629, A_11))), inference(superposition, [status(thm), theory('equality')], [c_4146, c_4184])).
% 5.54/2.10  tff(c_5607, plain, (![A_8620, A_8621]: (~r2_hidden('#skF_2'(A_8620, A_8620, k1_xboole_0), A_8621) | k4_xboole_0(A_8620, A_8620)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5563, c_4190])).
% 5.54/2.10  tff(c_5642, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5556, c_5607])).
% 5.54/2.10  tff(c_5708, plain, (![A_8833, C_8834]: (r2_hidden('#skF_2'(A_8833, A_8833, C_8834), C_8834) | k1_xboole_0=C_8834)), inference(demodulation, [status(thm), theory('equality')], [c_5642, c_5556])).
% 5.54/2.10  tff(c_6210, plain, (![A_9484, A_9485, B_9486]: (r2_hidden('#skF_2'(A_9484, A_9484, k4_xboole_0(A_9485, B_9486)), A_9485) | k4_xboole_0(A_9485, B_9486)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5708, c_8])).
% 5.54/2.10  tff(c_6501, plain, (![A_9648, A_9649, B_9650]: ('#skF_2'(A_9648, A_9648, k4_xboole_0(k1_tarski(A_9649), B_9650))=A_9649 | k4_xboole_0(k1_tarski(A_9649), B_9650)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6210, c_28])).
% 5.54/2.10  tff(c_5756, plain, (![A_8833, A_3, B_4]: (~r2_hidden('#skF_2'(A_8833, A_8833, k4_xboole_0(A_3, B_4)), B_4) | k4_xboole_0(A_3, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5708, c_6])).
% 5.54/2.10  tff(c_6513, plain, (![A_9649, B_9650]: (~r2_hidden(A_9649, B_9650) | k4_xboole_0(k1_tarski(A_9649), B_9650)=k1_xboole_0 | k4_xboole_0(k1_tarski(A_9649), B_9650)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6501, c_5756])).
% 5.54/2.10  tff(c_7105, plain, (![A_9917, B_9918]: (~r2_hidden(A_9917, B_9918) | k4_xboole_0(k1_tarski(A_9917), B_9918)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_6513])).
% 5.54/2.10  tff(c_4027, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 5.54/2.10  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.54/2.10  tff(c_4115, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4027, c_54])).
% 5.54/2.10  tff(c_7144, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7105, c_4115])).
% 5.54/2.10  tff(c_7224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4026, c_7144])).
% 5.54/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.10  
% 5.54/2.10  Inference rules
% 5.54/2.10  ----------------------
% 5.54/2.10  #Ref     : 0
% 5.54/2.10  #Sup     : 1072
% 5.54/2.10  #Fact    : 8
% 5.54/2.10  #Define  : 0
% 5.54/2.10  #Split   : 6
% 5.54/2.10  #Chain   : 0
% 5.54/2.10  #Close   : 0
% 5.54/2.10  
% 5.54/2.10  Ordering : KBO
% 5.54/2.10  
% 5.54/2.10  Simplification rules
% 5.54/2.10  ----------------------
% 5.54/2.10  #Subsume      : 151
% 5.54/2.10  #Demod        : 325
% 5.54/2.10  #Tautology    : 433
% 5.54/2.10  #SimpNegUnit  : 5
% 5.54/2.10  #BackRed      : 24
% 5.54/2.10  
% 5.54/2.10  #Partial instantiations: 3660
% 5.54/2.10  #Strategies tried      : 1
% 5.54/2.10  
% 5.54/2.10  Timing (in seconds)
% 5.54/2.10  ----------------------
% 5.54/2.10  Preprocessing        : 0.32
% 5.54/2.10  Parsing              : 0.16
% 5.54/2.10  CNF conversion       : 0.02
% 5.54/2.10  Main loop            : 1.01
% 5.54/2.10  Inferencing          : 0.47
% 5.54/2.10  Reduction            : 0.24
% 5.54/2.10  Demodulation         : 0.17
% 5.54/2.10  BG Simplification    : 0.05
% 5.54/2.10  Subsumption          : 0.17
% 5.54/2.10  Abstraction          : 0.05
% 5.54/2.10  MUC search           : 0.00
% 5.54/2.10  Cooper               : 0.00
% 5.54/2.10  Total                : 1.36
% 5.54/2.10  Index Insertion      : 0.00
% 5.54/2.10  Index Deletion       : 0.00
% 5.54/2.10  Index Matching       : 0.00
% 5.54/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
