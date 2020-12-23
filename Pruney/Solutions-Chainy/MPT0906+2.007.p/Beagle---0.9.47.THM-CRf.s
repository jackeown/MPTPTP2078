%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:54 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 256 expanded)
%              Number of leaves         :   31 (  96 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 456 expanded)
%              Number of equality atoms :   82 ( 388 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) != k1_xboole_0
       => ! [C] :
            ( m1_subset_1(C,k2_zfmisc_1(A,B))
           => ( C != k1_mcart_1(C)
              & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => ( C != k1_mcart_1(C)
                & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k3_xboole_0(A,B),C) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

tff(c_36,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_57,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_265,plain,(
    ! [C_82,A_83,B_84] :
      ( k1_mcart_1(C_82) != C_82
      | ~ m1_subset_1(C_82,k2_zfmisc_1(A_83,B_84))
      | k1_xboole_0 = B_84
      | k1_xboole_0 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_274,plain,
    ( k1_mcart_1('#skF_3') != '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_265])).

tff(c_277,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_274])).

tff(c_278,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_89])).

tff(c_101,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_281,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_101])).

tff(c_282,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_6])).

tff(c_26,plain,(
    ! [A_38,C_40,B_39] : k4_xboole_0(k2_zfmisc_1(A_38,C_40),k2_zfmisc_1(B_39,C_40)) = k2_zfmisc_1(k4_xboole_0(A_38,B_39),C_40) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_145,plain,(
    ! [A_74,C_75,B_76] : k3_xboole_0(k2_zfmisc_1(A_74,C_75),k2_zfmisc_1(B_76,C_75)) = k2_zfmisc_1(k3_xboole_0(A_74,B_76),C_75) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_155,plain,(
    ! [A_74,C_75,B_76] : k5_xboole_0(k2_zfmisc_1(A_74,C_75),k2_zfmisc_1(k3_xboole_0(A_74,B_76),C_75)) = k4_xboole_0(k2_zfmisc_1(A_74,C_75),k2_zfmisc_1(B_76,C_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_2])).

tff(c_4031,plain,(
    ! [A_147,C_148,B_149] : k5_xboole_0(k2_zfmisc_1(A_147,C_148),k2_zfmisc_1(k3_xboole_0(A_147,B_149),C_148)) = k2_zfmisc_1(k4_xboole_0(A_147,B_149),C_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_155])).

tff(c_4167,plain,(
    ! [A_3,C_148,B_4] : k5_xboole_0(k2_zfmisc_1(A_3,C_148),k2_zfmisc_1(A_3,C_148)) = k2_zfmisc_1(k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)),C_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4031])).

tff(c_4172,plain,(
    ! [C_148] : k2_zfmisc_1('#skF_1',C_148) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_282,c_4167])).

tff(c_40,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_283,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_40])).

tff(c_4176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4172,c_283])).

tff(c_4177,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_4182,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4177,c_101])).

tff(c_4183,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4177,c_6])).

tff(c_28,plain,(
    ! [C_40,A_38,B_39] : k4_xboole_0(k2_zfmisc_1(C_40,A_38),k2_zfmisc_1(C_40,B_39)) = k2_zfmisc_1(C_40,k4_xboole_0(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_133,plain,(
    ! [C_71,A_72,B_73] : k3_xboole_0(k2_zfmisc_1(C_71,A_72),k2_zfmisc_1(C_71,B_73)) = k2_zfmisc_1(C_71,k3_xboole_0(A_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,(
    ! [C_71,A_72,B_73] : k5_xboole_0(k2_zfmisc_1(C_71,A_72),k2_zfmisc_1(C_71,k3_xboole_0(A_72,B_73))) = k4_xboole_0(k2_zfmisc_1(C_71,A_72),k2_zfmisc_1(C_71,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_2])).

tff(c_7165,plain,(
    ! [C_210,A_211,B_212] : k5_xboole_0(k2_zfmisc_1(C_210,A_211),k2_zfmisc_1(C_210,k3_xboole_0(A_211,B_212))) = k2_zfmisc_1(C_210,k4_xboole_0(A_211,B_212)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_139])).

tff(c_7283,plain,(
    ! [C_210,A_3,B_4] : k5_xboole_0(k2_zfmisc_1(C_210,A_3),k2_zfmisc_1(C_210,A_3)) = k2_zfmisc_1(C_210,k4_xboole_0(A_3,k2_xboole_0(A_3,B_4))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7165])).

tff(c_7291,plain,(
    ! [C_210] : k2_zfmisc_1(C_210,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4182,c_4183,c_7283])).

tff(c_4184,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4177,c_40])).

tff(c_7295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7291,c_4184])).

tff(c_7296,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_7381,plain,(
    ! [C_236,A_237,B_238] :
      ( k2_mcart_1(C_236) != C_236
      | ~ m1_subset_1(C_236,k2_zfmisc_1(A_237,B_238))
      | k1_xboole_0 = B_238
      | k1_xboole_0 = A_237 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7384,plain,
    ( k2_mcart_1('#skF_3') != '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_7381])).

tff(c_7387,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7296,c_7384])).

tff(c_7388,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7387])).

tff(c_7329,plain,(
    ! [A_219,B_220] : k5_xboole_0(A_219,k3_xboole_0(A_219,B_220)) = k4_xboole_0(A_219,B_220) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7338,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7329])).

tff(c_7341,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7338])).

tff(c_7391,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7388,c_7341])).

tff(c_7392,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7388,c_6])).

tff(c_7425,plain,(
    ! [A_245,C_246,B_247] : k3_xboole_0(k2_zfmisc_1(A_245,C_246),k2_zfmisc_1(B_247,C_246)) = k2_zfmisc_1(k3_xboole_0(A_245,B_247),C_246) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7435,plain,(
    ! [A_245,C_246,B_247] : k5_xboole_0(k2_zfmisc_1(A_245,C_246),k2_zfmisc_1(k3_xboole_0(A_245,B_247),C_246)) = k4_xboole_0(k2_zfmisc_1(A_245,C_246),k2_zfmisc_1(B_247,C_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7425,c_2])).

tff(c_7870,plain,(
    ! [A_283,C_284,B_285] : k5_xboole_0(k2_zfmisc_1(A_283,C_284),k2_zfmisc_1(k3_xboole_0(A_283,B_285),C_284)) = k2_zfmisc_1(k4_xboole_0(A_283,B_285),C_284) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_7435])).

tff(c_7918,plain,(
    ! [A_3,C_284,B_4] : k5_xboole_0(k2_zfmisc_1(A_3,C_284),k2_zfmisc_1(A_3,C_284)) = k2_zfmisc_1(k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)),C_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7870])).

tff(c_7926,plain,(
    ! [C_284] : k2_zfmisc_1('#skF_1',C_284) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7391,c_7392,c_7918])).

tff(c_7393,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7388,c_40])).

tff(c_7930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7926,c_7393])).

tff(c_7931,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7387])).

tff(c_7935,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7931,c_7341])).

tff(c_7936,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7931,c_6])).

tff(c_7957,plain,(
    ! [C_289,A_290,B_291] : k3_xboole_0(k2_zfmisc_1(C_289,A_290),k2_zfmisc_1(C_289,B_291)) = k2_zfmisc_1(C_289,k3_xboole_0(A_290,B_291)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7963,plain,(
    ! [C_289,A_290,B_291] : k5_xboole_0(k2_zfmisc_1(C_289,A_290),k2_zfmisc_1(C_289,k3_xboole_0(A_290,B_291))) = k4_xboole_0(k2_zfmisc_1(C_289,A_290),k2_zfmisc_1(C_289,B_291)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7957,c_2])).

tff(c_8265,plain,(
    ! [C_313,A_314,B_315] : k5_xboole_0(k2_zfmisc_1(C_313,A_314),k2_zfmisc_1(C_313,k3_xboole_0(A_314,B_315))) = k2_zfmisc_1(C_313,k4_xboole_0(A_314,B_315)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7963])).

tff(c_8303,plain,(
    ! [C_313,A_3,B_4] : k5_xboole_0(k2_zfmisc_1(C_313,A_3),k2_zfmisc_1(C_313,A_3)) = k2_zfmisc_1(C_313,k4_xboole_0(A_3,k2_xboole_0(A_3,B_4))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8265])).

tff(c_8308,plain,(
    ! [C_313] : k2_zfmisc_1(C_313,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7935,c_7936,c_8303])).

tff(c_7937,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7931,c_40])).

tff(c_8312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8308,c_7937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:08:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.41/2.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.77  
% 7.41/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.77  %$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.41/2.77  
% 7.41/2.77  %Foreground sorts:
% 7.41/2.77  
% 7.41/2.77  
% 7.41/2.77  %Background operators:
% 7.41/2.77  
% 7.41/2.77  
% 7.41/2.77  %Foreground operators:
% 7.41/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.41/2.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.41/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.41/2.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.41/2.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.41/2.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.41/2.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.41/2.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.41/2.77  tff('#skF_2', type, '#skF_2': $i).
% 7.41/2.77  tff('#skF_3', type, '#skF_3': $i).
% 7.41/2.77  tff('#skF_1', type, '#skF_1': $i).
% 7.41/2.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.41/2.77  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.41/2.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.41/2.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.41/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.41/2.77  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.41/2.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.41/2.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.41/2.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.41/2.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.41/2.77  
% 7.41/2.79  tff(f_85, negated_conjecture, ~(![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_mcart_1)).
% 7.41/2.79  tff(f_72, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 7.41/2.79  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.41/2.79  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 7.41/2.79  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.41/2.79  tff(f_53, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 7.41/2.79  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k3_xboole_0(A, B), C) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_zfmisc_1)).
% 7.41/2.79  tff(c_36, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.41/2.79  tff(c_57, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_36])).
% 7.41/2.79  tff(c_38, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.41/2.79  tff(c_265, plain, (![C_82, A_83, B_84]: (k1_mcart_1(C_82)!=C_82 | ~m1_subset_1(C_82, k2_zfmisc_1(A_83, B_84)) | k1_xboole_0=B_84 | k1_xboole_0=A_83)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.41/2.79  tff(c_274, plain, (k1_mcart_1('#skF_3')!='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_38, c_265])).
% 7.41/2.79  tff(c_277, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_274])).
% 7.41/2.79  tff(c_278, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_277])).
% 7.41/2.79  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.41/2.79  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.41/2.79  tff(c_89, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.79  tff(c_98, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_89])).
% 7.41/2.79  tff(c_101, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_98])).
% 7.41/2.79  tff(c_281, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_101])).
% 7.41/2.79  tff(c_282, plain, (![A_5]: (k5_xboole_0(A_5, A_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_6])).
% 7.41/2.79  tff(c_26, plain, (![A_38, C_40, B_39]: (k4_xboole_0(k2_zfmisc_1(A_38, C_40), k2_zfmisc_1(B_39, C_40))=k2_zfmisc_1(k4_xboole_0(A_38, B_39), C_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.41/2.79  tff(c_145, plain, (![A_74, C_75, B_76]: (k3_xboole_0(k2_zfmisc_1(A_74, C_75), k2_zfmisc_1(B_76, C_75))=k2_zfmisc_1(k3_xboole_0(A_74, B_76), C_75))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.41/2.79  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.79  tff(c_155, plain, (![A_74, C_75, B_76]: (k5_xboole_0(k2_zfmisc_1(A_74, C_75), k2_zfmisc_1(k3_xboole_0(A_74, B_76), C_75))=k4_xboole_0(k2_zfmisc_1(A_74, C_75), k2_zfmisc_1(B_76, C_75)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_2])).
% 7.41/2.79  tff(c_4031, plain, (![A_147, C_148, B_149]: (k5_xboole_0(k2_zfmisc_1(A_147, C_148), k2_zfmisc_1(k3_xboole_0(A_147, B_149), C_148))=k2_zfmisc_1(k4_xboole_0(A_147, B_149), C_148))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_155])).
% 7.41/2.79  tff(c_4167, plain, (![A_3, C_148, B_4]: (k5_xboole_0(k2_zfmisc_1(A_3, C_148), k2_zfmisc_1(A_3, C_148))=k2_zfmisc_1(k4_xboole_0(A_3, k2_xboole_0(A_3, B_4)), C_148))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4031])).
% 7.41/2.79  tff(c_4172, plain, (![C_148]: (k2_zfmisc_1('#skF_1', C_148)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_282, c_4167])).
% 7.41/2.79  tff(c_40, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.41/2.79  tff(c_283, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_40])).
% 7.41/2.79  tff(c_4176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4172, c_283])).
% 7.41/2.79  tff(c_4177, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_277])).
% 7.41/2.79  tff(c_4182, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4177, c_101])).
% 7.41/2.79  tff(c_4183, plain, (![A_5]: (k5_xboole_0(A_5, A_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4177, c_6])).
% 7.41/2.79  tff(c_28, plain, (![C_40, A_38, B_39]: (k4_xboole_0(k2_zfmisc_1(C_40, A_38), k2_zfmisc_1(C_40, B_39))=k2_zfmisc_1(C_40, k4_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.41/2.79  tff(c_133, plain, (![C_71, A_72, B_73]: (k3_xboole_0(k2_zfmisc_1(C_71, A_72), k2_zfmisc_1(C_71, B_73))=k2_zfmisc_1(C_71, k3_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.41/2.79  tff(c_139, plain, (![C_71, A_72, B_73]: (k5_xboole_0(k2_zfmisc_1(C_71, A_72), k2_zfmisc_1(C_71, k3_xboole_0(A_72, B_73)))=k4_xboole_0(k2_zfmisc_1(C_71, A_72), k2_zfmisc_1(C_71, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_2])).
% 7.41/2.79  tff(c_7165, plain, (![C_210, A_211, B_212]: (k5_xboole_0(k2_zfmisc_1(C_210, A_211), k2_zfmisc_1(C_210, k3_xboole_0(A_211, B_212)))=k2_zfmisc_1(C_210, k4_xboole_0(A_211, B_212)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_139])).
% 7.41/2.79  tff(c_7283, plain, (![C_210, A_3, B_4]: (k5_xboole_0(k2_zfmisc_1(C_210, A_3), k2_zfmisc_1(C_210, A_3))=k2_zfmisc_1(C_210, k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7165])).
% 7.41/2.79  tff(c_7291, plain, (![C_210]: (k2_zfmisc_1(C_210, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4182, c_4183, c_7283])).
% 7.41/2.79  tff(c_4184, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4177, c_40])).
% 7.41/2.79  tff(c_7295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7291, c_4184])).
% 7.41/2.79  tff(c_7296, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 7.41/2.79  tff(c_7381, plain, (![C_236, A_237, B_238]: (k2_mcart_1(C_236)!=C_236 | ~m1_subset_1(C_236, k2_zfmisc_1(A_237, B_238)) | k1_xboole_0=B_238 | k1_xboole_0=A_237)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.41/2.79  tff(c_7384, plain, (k2_mcart_1('#skF_3')!='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_38, c_7381])).
% 7.41/2.79  tff(c_7387, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7296, c_7384])).
% 7.41/2.79  tff(c_7388, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_7387])).
% 7.41/2.79  tff(c_7329, plain, (![A_219, B_220]: (k5_xboole_0(A_219, k3_xboole_0(A_219, B_220))=k4_xboole_0(A_219, B_220))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.79  tff(c_7338, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7329])).
% 7.41/2.79  tff(c_7341, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7338])).
% 7.41/2.79  tff(c_7391, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7388, c_7341])).
% 7.41/2.79  tff(c_7392, plain, (![A_5]: (k5_xboole_0(A_5, A_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7388, c_6])).
% 7.41/2.79  tff(c_7425, plain, (![A_245, C_246, B_247]: (k3_xboole_0(k2_zfmisc_1(A_245, C_246), k2_zfmisc_1(B_247, C_246))=k2_zfmisc_1(k3_xboole_0(A_245, B_247), C_246))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.41/2.79  tff(c_7435, plain, (![A_245, C_246, B_247]: (k5_xboole_0(k2_zfmisc_1(A_245, C_246), k2_zfmisc_1(k3_xboole_0(A_245, B_247), C_246))=k4_xboole_0(k2_zfmisc_1(A_245, C_246), k2_zfmisc_1(B_247, C_246)))), inference(superposition, [status(thm), theory('equality')], [c_7425, c_2])).
% 7.41/2.79  tff(c_7870, plain, (![A_283, C_284, B_285]: (k5_xboole_0(k2_zfmisc_1(A_283, C_284), k2_zfmisc_1(k3_xboole_0(A_283, B_285), C_284))=k2_zfmisc_1(k4_xboole_0(A_283, B_285), C_284))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_7435])).
% 7.41/2.79  tff(c_7918, plain, (![A_3, C_284, B_4]: (k5_xboole_0(k2_zfmisc_1(A_3, C_284), k2_zfmisc_1(A_3, C_284))=k2_zfmisc_1(k4_xboole_0(A_3, k2_xboole_0(A_3, B_4)), C_284))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7870])).
% 7.41/2.79  tff(c_7926, plain, (![C_284]: (k2_zfmisc_1('#skF_1', C_284)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7391, c_7392, c_7918])).
% 7.41/2.79  tff(c_7393, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7388, c_40])).
% 7.41/2.79  tff(c_7930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7926, c_7393])).
% 7.41/2.79  tff(c_7931, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7387])).
% 7.41/2.79  tff(c_7935, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7931, c_7341])).
% 7.41/2.79  tff(c_7936, plain, (![A_5]: (k5_xboole_0(A_5, A_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7931, c_6])).
% 7.41/2.79  tff(c_7957, plain, (![C_289, A_290, B_291]: (k3_xboole_0(k2_zfmisc_1(C_289, A_290), k2_zfmisc_1(C_289, B_291))=k2_zfmisc_1(C_289, k3_xboole_0(A_290, B_291)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.41/2.79  tff(c_7963, plain, (![C_289, A_290, B_291]: (k5_xboole_0(k2_zfmisc_1(C_289, A_290), k2_zfmisc_1(C_289, k3_xboole_0(A_290, B_291)))=k4_xboole_0(k2_zfmisc_1(C_289, A_290), k2_zfmisc_1(C_289, B_291)))), inference(superposition, [status(thm), theory('equality')], [c_7957, c_2])).
% 7.41/2.79  tff(c_8265, plain, (![C_313, A_314, B_315]: (k5_xboole_0(k2_zfmisc_1(C_313, A_314), k2_zfmisc_1(C_313, k3_xboole_0(A_314, B_315)))=k2_zfmisc_1(C_313, k4_xboole_0(A_314, B_315)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7963])).
% 7.41/2.79  tff(c_8303, plain, (![C_313, A_3, B_4]: (k5_xboole_0(k2_zfmisc_1(C_313, A_3), k2_zfmisc_1(C_313, A_3))=k2_zfmisc_1(C_313, k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8265])).
% 7.41/2.79  tff(c_8308, plain, (![C_313]: (k2_zfmisc_1(C_313, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7935, c_7936, c_8303])).
% 7.41/2.79  tff(c_7937, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7931, c_40])).
% 7.41/2.79  tff(c_8312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8308, c_7937])).
% 7.41/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.79  
% 7.41/2.79  Inference rules
% 7.41/2.79  ----------------------
% 7.41/2.79  #Ref     : 0
% 7.41/2.79  #Sup     : 2216
% 7.41/2.79  #Fact    : 0
% 7.41/2.79  #Define  : 0
% 7.41/2.79  #Split   : 4
% 7.41/2.79  #Chain   : 0
% 7.41/2.79  #Close   : 0
% 7.41/2.79  
% 7.41/2.79  Ordering : KBO
% 7.41/2.79  
% 7.41/2.79  Simplification rules
% 7.41/2.79  ----------------------
% 7.41/2.79  #Subsume      : 61
% 7.41/2.79  #Demod        : 640
% 7.41/2.79  #Tautology    : 287
% 7.41/2.79  #SimpNegUnit  : 4
% 7.41/2.79  #BackRed      : 29
% 7.41/2.79  
% 7.41/2.79  #Partial instantiations: 0
% 7.41/2.79  #Strategies tried      : 1
% 7.41/2.79  
% 7.41/2.79  Timing (in seconds)
% 7.41/2.79  ----------------------
% 7.41/2.79  Preprocessing        : 0.31
% 7.41/2.79  Parsing              : 0.17
% 7.41/2.79  CNF conversion       : 0.02
% 7.41/2.79  Main loop            : 1.68
% 7.41/2.79  Inferencing          : 0.52
% 7.41/2.79  Reduction            : 0.77
% 7.41/2.79  Demodulation         : 0.67
% 7.41/2.79  BG Simplification    : 0.11
% 7.41/2.79  Subsumption          : 0.20
% 7.41/2.79  Abstraction          : 0.13
% 7.41/2.79  MUC search           : 0.00
% 7.41/2.79  Cooper               : 0.00
% 7.41/2.79  Total                : 2.03
% 7.41/2.79  Index Insertion      : 0.00
% 7.41/2.79  Index Deletion       : 0.00
% 7.41/2.79  Index Matching       : 0.00
% 7.41/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
