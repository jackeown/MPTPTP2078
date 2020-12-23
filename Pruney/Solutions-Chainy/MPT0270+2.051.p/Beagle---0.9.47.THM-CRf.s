%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:59 EST 2020

% Result     : Theorem 6.37s
% Output     : CNFRefutation 6.37s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 150 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 194 expanded)
%              Number of equality atoms :   40 (  70 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7833,plain,(
    ! [A_352,B_353] : k5_xboole_0(A_352,k3_xboole_0(A_352,B_353)) = k4_xboole_0(A_352,B_353) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7851,plain,(
    ! [A_354] : k5_xboole_0(A_354,A_354) = k4_xboole_0(A_354,A_354) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7833])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7858,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7851,c_18])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7880,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7858,c_20])).

tff(c_7905,plain,(
    ! [A_365,B_366,C_367] :
      ( ~ r1_xboole_0(A_365,B_366)
      | ~ r2_hidden(C_367,k3_xboole_0(A_365,B_366)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7920,plain,(
    ! [A_368,C_369] :
      ( ~ r1_xboole_0(A_368,A_368)
      | ~ r2_hidden(C_369,A_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7905])).

tff(c_7926,plain,(
    ! [C_369] : ~ r2_hidden(C_369,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7880,c_7920])).

tff(c_5509,plain,(
    ! [A_241,B_242] : k5_xboole_0(A_241,k3_xboole_0(A_241,B_242)) = k4_xboole_0(A_241,B_242) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5527,plain,(
    ! [A_243] : k5_xboole_0(A_243,A_243) = k4_xboole_0(A_243,A_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5509])).

tff(c_5534,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5527,c_18])).

tff(c_5547,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5534,c_20])).

tff(c_5575,plain,(
    ! [A_249,B_250,C_251] :
      ( ~ r1_xboole_0(A_249,B_250)
      | ~ r2_hidden(C_251,k3_xboole_0(A_249,B_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5604,plain,(
    ! [A_257,C_258] :
      ( ~ r1_xboole_0(A_257,A_257)
      | ~ r2_hidden(C_258,A_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5575])).

tff(c_5610,plain,(
    ! [C_258] : ~ r2_hidden(C_258,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5547,c_5604])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_40,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(k1_tarski(A_51),B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_226,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_258,plain,(
    ! [A_89,B_90] :
      ( ~ r1_xboole_0(A_89,B_90)
      | k3_xboole_0(A_89,B_90) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_1055,plain,(
    ! [A_155,B_156] :
      ( k3_xboole_0(k1_tarski(A_155),B_156) = k1_xboole_0
      | r2_hidden(A_155,B_156) ) ),
    inference(resolution,[status(thm)],[c_40,c_258])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1091,plain,(
    ! [A_155,B_156] :
      ( k5_xboole_0(k1_tarski(A_155),k1_xboole_0) = k4_xboole_0(k1_tarski(A_155),B_156)
      | r2_hidden(A_155,B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_12])).

tff(c_5335,plain,(
    ! [A_225,B_226] :
      ( k4_xboole_0(k1_tarski(A_225),B_226) = k1_tarski(A_225)
      | r2_hidden(A_225,B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1091])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_128,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_5404,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5335,c_128])).

tff(c_5444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_5404])).

tff(c_5445,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_38,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k1_tarski(A_49),B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5482,plain,(
    ! [A_237,B_238] :
      ( k3_xboole_0(A_237,B_238) = A_237
      | ~ r1_tarski(A_237,B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7561,plain,(
    ! [A_333,B_334] :
      ( k3_xboole_0(k1_tarski(A_333),B_334) = k1_tarski(A_333)
      | ~ r2_hidden(A_333,B_334) ) ),
    inference(resolution,[status(thm)],[c_38,c_5482])).

tff(c_5446,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5552,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5446,c_52])).

tff(c_5556,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5552,c_20])).

tff(c_5629,plain,(
    ! [A_263,B_264] :
      ( ~ r1_xboole_0(A_263,B_264)
      | k3_xboole_0(A_263,B_264) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_5575])).

tff(c_5645,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5556,c_5629])).

tff(c_7615,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7561,c_5645])).

tff(c_7676,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5445,c_7615])).

tff(c_83,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),A_61) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_83])).

tff(c_5470,plain,(
    ! [A_232,B_233] :
      ( r2_hidden(A_232,B_233)
      | ~ r1_tarski(k1_tarski(A_232),B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5479,plain,(
    ! [A_232] : r2_hidden(A_232,k1_tarski(A_232)) ),
    inference(resolution,[status(thm)],[c_86,c_5470])).

tff(c_7712,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7676,c_5479])).

tff(c_7725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5610,c_7712])).

tff(c_7726,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_7815,plain,(
    ! [A_348,B_349] :
      ( r1_tarski(k1_tarski(A_348),B_349)
      | ~ r2_hidden(A_348,B_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9255,plain,(
    ! [A_438,B_439] :
      ( k3_xboole_0(k1_tarski(A_438),B_439) = k1_tarski(A_438)
      | ~ r2_hidden(A_438,B_439) ) ),
    inference(resolution,[status(thm)],[c_7815,c_16])).

tff(c_7727,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7729,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7727,c_54])).

tff(c_7733,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7729,c_20])).

tff(c_7945,plain,(
    ! [A_374,B_375] :
      ( ~ r1_xboole_0(A_374,B_375)
      | k3_xboole_0(A_374,B_375) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_7905])).

tff(c_7961,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7733,c_7945])).

tff(c_9297,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9255,c_7961])).

tff(c_9355,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7726,c_9297])).

tff(c_7792,plain,(
    ! [A_341,B_342] :
      ( r2_hidden(A_341,B_342)
      | ~ r1_tarski(k1_tarski(A_341),B_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7797,plain,(
    ! [A_341] : r2_hidden(A_341,k1_tarski(A_341)) ),
    inference(resolution,[status(thm)],[c_86,c_7792])).

tff(c_9394,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9355,c_7797])).

tff(c_9405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7926,c_9394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.37/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.46  
% 6.37/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 6.37/2.46  
% 6.37/2.46  %Foreground sorts:
% 6.37/2.46  
% 6.37/2.46  
% 6.37/2.46  %Background operators:
% 6.37/2.46  
% 6.37/2.46  
% 6.37/2.46  %Foreground operators:
% 6.37/2.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.37/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.37/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.37/2.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.37/2.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.37/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.37/2.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.37/2.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.37/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.37/2.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.37/2.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.37/2.46  tff('#skF_5', type, '#skF_5': $i).
% 6.37/2.46  tff('#skF_6', type, '#skF_6': $i).
% 6.37/2.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.37/2.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.37/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.37/2.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.37/2.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.37/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.37/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.37/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.37/2.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.37/2.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.37/2.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.37/2.46  
% 6.37/2.48  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.37/2.48  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.37/2.48  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.37/2.48  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.37/2.48  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.37/2.48  tff(f_98, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 6.37/2.48  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.37/2.48  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.37/2.48  tff(f_81, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.37/2.48  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.37/2.48  tff(f_55, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.37/2.48  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.37/2.48  tff(c_7833, plain, (![A_352, B_353]: (k5_xboole_0(A_352, k3_xboole_0(A_352, B_353))=k4_xboole_0(A_352, B_353))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.37/2.48  tff(c_7851, plain, (![A_354]: (k5_xboole_0(A_354, A_354)=k4_xboole_0(A_354, A_354))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7833])).
% 6.37/2.48  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.37/2.48  tff(c_7858, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7851, c_18])).
% 6.37/2.48  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.37/2.48  tff(c_7880, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7858, c_20])).
% 6.37/2.48  tff(c_7905, plain, (![A_365, B_366, C_367]: (~r1_xboole_0(A_365, B_366) | ~r2_hidden(C_367, k3_xboole_0(A_365, B_366)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.37/2.48  tff(c_7920, plain, (![A_368, C_369]: (~r1_xboole_0(A_368, A_368) | ~r2_hidden(C_369, A_368))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7905])).
% 6.37/2.48  tff(c_7926, plain, (![C_369]: (~r2_hidden(C_369, k1_xboole_0))), inference(resolution, [status(thm)], [c_7880, c_7920])).
% 6.37/2.48  tff(c_5509, plain, (![A_241, B_242]: (k5_xboole_0(A_241, k3_xboole_0(A_241, B_242))=k4_xboole_0(A_241, B_242))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.37/2.48  tff(c_5527, plain, (![A_243]: (k5_xboole_0(A_243, A_243)=k4_xboole_0(A_243, A_243))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5509])).
% 6.37/2.48  tff(c_5534, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5527, c_18])).
% 6.37/2.48  tff(c_5547, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5534, c_20])).
% 6.37/2.48  tff(c_5575, plain, (![A_249, B_250, C_251]: (~r1_xboole_0(A_249, B_250) | ~r2_hidden(C_251, k3_xboole_0(A_249, B_250)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.37/2.48  tff(c_5604, plain, (![A_257, C_258]: (~r1_xboole_0(A_257, A_257) | ~r2_hidden(C_258, A_257))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5575])).
% 6.37/2.48  tff(c_5610, plain, (![C_258]: (~r2_hidden(C_258, k1_xboole_0))), inference(resolution, [status(thm)], [c_5547, c_5604])).
% 6.37/2.48  tff(c_50, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.37/2.48  tff(c_87, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 6.37/2.48  tff(c_40, plain, (![A_51, B_52]: (r1_xboole_0(k1_tarski(A_51), B_52) | r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.37/2.48  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.37/2.48  tff(c_226, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.37/2.48  tff(c_258, plain, (![A_89, B_90]: (~r1_xboole_0(A_89, B_90) | k3_xboole_0(A_89, B_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_226])).
% 6.37/2.48  tff(c_1055, plain, (![A_155, B_156]: (k3_xboole_0(k1_tarski(A_155), B_156)=k1_xboole_0 | r2_hidden(A_155, B_156))), inference(resolution, [status(thm)], [c_40, c_258])).
% 6.37/2.48  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.37/2.48  tff(c_1091, plain, (![A_155, B_156]: (k5_xboole_0(k1_tarski(A_155), k1_xboole_0)=k4_xboole_0(k1_tarski(A_155), B_156) | r2_hidden(A_155, B_156))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_12])).
% 6.37/2.48  tff(c_5335, plain, (![A_225, B_226]: (k4_xboole_0(k1_tarski(A_225), B_226)=k1_tarski(A_225) | r2_hidden(A_225, B_226))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1091])).
% 6.37/2.48  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.37/2.48  tff(c_128, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 6.37/2.48  tff(c_5404, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5335, c_128])).
% 6.37/2.48  tff(c_5444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_5404])).
% 6.37/2.48  tff(c_5445, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 6.37/2.48  tff(c_38, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), B_50) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.37/2.48  tff(c_5482, plain, (![A_237, B_238]: (k3_xboole_0(A_237, B_238)=A_237 | ~r1_tarski(A_237, B_238))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.37/2.48  tff(c_7561, plain, (![A_333, B_334]: (k3_xboole_0(k1_tarski(A_333), B_334)=k1_tarski(A_333) | ~r2_hidden(A_333, B_334))), inference(resolution, [status(thm)], [c_38, c_5482])).
% 6.37/2.48  tff(c_5446, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 6.37/2.48  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.37/2.48  tff(c_5552, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5446, c_52])).
% 6.37/2.48  tff(c_5556, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5552, c_20])).
% 6.37/2.48  tff(c_5629, plain, (![A_263, B_264]: (~r1_xboole_0(A_263, B_264) | k3_xboole_0(A_263, B_264)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_5575])).
% 6.37/2.48  tff(c_5645, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_5556, c_5629])).
% 6.37/2.48  tff(c_7615, plain, (k1_tarski('#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7561, c_5645])).
% 6.37/2.48  tff(c_7676, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5445, c_7615])).
% 6.37/2.48  tff(c_83, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), A_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.37/2.48  tff(c_86, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_83])).
% 6.37/2.48  tff(c_5470, plain, (![A_232, B_233]: (r2_hidden(A_232, B_233) | ~r1_tarski(k1_tarski(A_232), B_233))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.37/2.48  tff(c_5479, plain, (![A_232]: (r2_hidden(A_232, k1_tarski(A_232)))), inference(resolution, [status(thm)], [c_86, c_5470])).
% 6.37/2.48  tff(c_7712, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7676, c_5479])).
% 6.37/2.48  tff(c_7725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5610, c_7712])).
% 6.37/2.48  tff(c_7726, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 6.37/2.48  tff(c_7815, plain, (![A_348, B_349]: (r1_tarski(k1_tarski(A_348), B_349) | ~r2_hidden(A_348, B_349))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.37/2.48  tff(c_16, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.37/2.48  tff(c_9255, plain, (![A_438, B_439]: (k3_xboole_0(k1_tarski(A_438), B_439)=k1_tarski(A_438) | ~r2_hidden(A_438, B_439))), inference(resolution, [status(thm)], [c_7815, c_16])).
% 6.37/2.48  tff(c_7727, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 6.37/2.48  tff(c_54, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.37/2.48  tff(c_7729, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7727, c_54])).
% 6.37/2.48  tff(c_7733, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7729, c_20])).
% 6.37/2.48  tff(c_7945, plain, (![A_374, B_375]: (~r1_xboole_0(A_374, B_375) | k3_xboole_0(A_374, B_375)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_7905])).
% 6.37/2.48  tff(c_7961, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_7733, c_7945])).
% 6.37/2.48  tff(c_9297, plain, (k1_tarski('#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9255, c_7961])).
% 6.37/2.48  tff(c_9355, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7726, c_9297])).
% 6.37/2.48  tff(c_7792, plain, (![A_341, B_342]: (r2_hidden(A_341, B_342) | ~r1_tarski(k1_tarski(A_341), B_342))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.37/2.48  tff(c_7797, plain, (![A_341]: (r2_hidden(A_341, k1_tarski(A_341)))), inference(resolution, [status(thm)], [c_86, c_7792])).
% 6.37/2.48  tff(c_9394, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9355, c_7797])).
% 6.37/2.48  tff(c_9405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7926, c_9394])).
% 6.37/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.48  
% 6.37/2.48  Inference rules
% 6.37/2.48  ----------------------
% 6.37/2.48  #Ref     : 0
% 6.37/2.48  #Sup     : 2334
% 6.37/2.48  #Fact    : 0
% 6.37/2.48  #Define  : 0
% 6.37/2.48  #Split   : 2
% 6.37/2.48  #Chain   : 0
% 6.37/2.48  #Close   : 0
% 6.37/2.48  
% 6.37/2.48  Ordering : KBO
% 6.37/2.48  
% 6.37/2.48  Simplification rules
% 6.37/2.48  ----------------------
% 6.37/2.48  #Subsume      : 253
% 6.37/2.48  #Demod        : 2032
% 6.37/2.48  #Tautology    : 1482
% 6.37/2.48  #SimpNegUnit  : 53
% 6.37/2.48  #BackRed      : 12
% 6.37/2.48  
% 6.37/2.48  #Partial instantiations: 0
% 6.37/2.48  #Strategies tried      : 1
% 6.37/2.48  
% 6.37/2.48  Timing (in seconds)
% 6.37/2.48  ----------------------
% 6.37/2.48  Preprocessing        : 0.40
% 6.37/2.48  Parsing              : 0.23
% 6.37/2.48  CNF conversion       : 0.03
% 6.37/2.48  Main loop            : 1.20
% 6.37/2.48  Inferencing          : 0.37
% 6.37/2.48  Reduction            : 0.53
% 6.37/2.48  Demodulation         : 0.43
% 6.37/2.48  BG Simplification    : 0.04
% 6.37/2.48  Subsumption          : 0.17
% 6.37/2.48  Abstraction          : 0.06
% 6.37/2.48  MUC search           : 0.00
% 6.37/2.48  Cooper               : 0.00
% 6.37/2.48  Total                : 1.63
% 6.37/2.48  Index Insertion      : 0.00
% 6.37/2.48  Index Deletion       : 0.00
% 6.37/2.48  Index Matching       : 0.00
% 6.37/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
