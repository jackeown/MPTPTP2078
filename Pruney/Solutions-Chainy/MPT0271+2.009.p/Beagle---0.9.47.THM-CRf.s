%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:02 EST 2020

% Result     : Theorem 9.87s
% Output     : CNFRefutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 313 expanded)
%              Number of leaves         :   36 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 ( 324 expanded)
%              Number of equality atoms :   86 ( 272 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_48,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_205,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [B_63,A_64] : k5_xboole_0(B_63,A_64) = k5_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_12])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_500,plain,(
    ! [A_101,B_102,C_103] : k5_xboole_0(k5_xboole_0(A_101,B_102),C_103) = k5_xboole_0(A_101,k5_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_564,plain,(
    ! [A_15,C_103] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_103)) = k5_xboole_0(k1_xboole_0,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_500])).

tff(c_578,plain,(
    ! [A_104,C_105] : k5_xboole_0(A_104,k5_xboole_0(A_104,C_105)) = C_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_564])).

tff(c_621,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_578])).

tff(c_643,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k5_xboole_0(B_107,A_106)) = B_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_578])).

tff(c_670,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),B_2) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_643])).

tff(c_20,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_242,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_279,plain,(
    ! [B_73,A_74] : k3_tarski(k2_tarski(B_73,A_74)) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_242])).

tff(c_38,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_285,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_38])).

tff(c_52,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_365,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_722,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k2_xboole_0(A_108,B_109)) = k3_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3599,plain,(
    ! [A_173,B_174] : k5_xboole_0(A_173,k5_xboole_0(B_174,k2_xboole_0(A_173,B_174))) = k3_xboole_0(A_173,B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_14])).

tff(c_577,plain,(
    ! [A_15,C_103] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_103)) = C_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_564])).

tff(c_3639,plain,(
    ! [B_174,A_173] : k5_xboole_0(B_174,k2_xboole_0(A_173,B_174)) = k5_xboole_0(A_173,k3_xboole_0(A_173,B_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3599,c_577])).

tff(c_3733,plain,(
    ! [B_175,A_176] : k5_xboole_0(B_175,k2_xboole_0(A_176,B_175)) = k4_xboole_0(A_176,B_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3639])).

tff(c_3891,plain,(
    ! [A_178,B_179] : k5_xboole_0(k2_xboole_0(A_178,B_179),k4_xboole_0(A_178,B_179)) = B_179 ),
    inference(superposition,[status(thm),theory(equality)],[c_3733,c_621])).

tff(c_3945,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_3891])).

tff(c_3964,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_285,c_3945])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k2_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3975,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k1_tarski('#skF_3')),'#skF_4') = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3964,c_18])).

tff(c_3978,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_3975])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3998,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3978,c_10])).

tff(c_22,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_340,plain,(
    ! [A_77,C_78,B_79] :
      ( r2_hidden(A_77,C_78)
      | ~ r1_tarski(k2_tarski(A_77,B_79),C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_353,plain,(
    ! [A_20,C_78] :
      ( r2_hidden(A_20,C_78)
      | ~ r1_tarski(k1_tarski(A_20),C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_340])).

tff(c_4007,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_3998,c_353])).

tff(c_4011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_4007])).

tff(c_4012,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4367,plain,(
    ! [A_206,B_207] : k5_xboole_0(k5_xboole_0(A_206,B_207),k2_xboole_0(A_206,B_207)) = k3_xboole_0(A_206,B_207) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6924,plain,(
    ! [A_272,B_273] : k5_xboole_0(A_272,k5_xboole_0(B_273,k2_xboole_0(A_272,B_273))) = k3_xboole_0(A_272,B_273) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4367])).

tff(c_4144,plain,(
    ! [A_199,B_200,C_201] : k5_xboole_0(k5_xboole_0(A_199,B_200),C_201) = k5_xboole_0(A_199,k5_xboole_0(B_200,C_201)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4208,plain,(
    ! [A_15,C_201] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_201)) = k5_xboole_0(k1_xboole_0,C_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4144])).

tff(c_4221,plain,(
    ! [A_15,C_201] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_201)) = C_201 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_4208])).

tff(c_6952,plain,(
    ! [B_273,A_272] : k5_xboole_0(B_273,k2_xboole_0(A_272,B_273)) = k5_xboole_0(A_272,k3_xboole_0(A_272,B_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6924,c_4221])).

tff(c_7037,plain,(
    ! [B_274,A_275] : k5_xboole_0(B_274,k2_xboole_0(A_275,B_274)) = k4_xboole_0(A_275,B_274) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6952])).

tff(c_7081,plain,(
    ! [B_274,A_275] : k5_xboole_0(B_274,k4_xboole_0(A_275,B_274)) = k2_xboole_0(A_275,B_274) ),
    inference(superposition,[status(thm),theory(equality)],[c_7037,c_4221])).

tff(c_4110,plain,(
    ! [B_195,A_196] :
      ( k3_xboole_0(B_195,k1_tarski(A_196)) = k1_tarski(A_196)
      | ~ r2_hidden(A_196,B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12856,plain,(
    ! [B_335,A_336] :
      ( k5_xboole_0(B_335,k1_tarski(A_336)) = k4_xboole_0(B_335,k1_tarski(A_336))
      | ~ r2_hidden(A_336,B_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4110,c_8])).

tff(c_4222,plain,(
    ! [A_202,C_203] : k5_xboole_0(A_202,k5_xboole_0(A_202,C_203)) = C_203 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_4208])).

tff(c_4265,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4222])).

tff(c_12970,plain,(
    ! [A_336,B_335] :
      ( k5_xboole_0(k1_tarski(A_336),k4_xboole_0(B_335,k1_tarski(A_336))) = B_335
      | ~ r2_hidden(A_336,B_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12856,c_4265])).

tff(c_13121,plain,(
    ! [B_337,A_338] :
      ( k2_xboole_0(B_337,k1_tarski(A_338)) = B_337
      | ~ r2_hidden(A_338,B_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7081,c_12970])).

tff(c_7123,plain,(
    ! [A_74,B_73] : k5_xboole_0(A_74,k2_xboole_0(A_74,B_73)) = k4_xboole_0(B_73,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_7037])).

tff(c_13149,plain,(
    ! [B_337,A_338] :
      ( k5_xboole_0(B_337,B_337) = k4_xboole_0(k1_tarski(A_338),B_337)
      | ~ r2_hidden(A_338,B_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13121,c_7123])).

tff(c_13668,plain,(
    ! [A_344,B_345] :
      ( k4_xboole_0(k1_tarski(A_344),B_345) = k1_xboole_0
      | ~ r2_hidden(A_344,B_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_13149])).

tff(c_4013,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4029,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4013,c_50])).

tff(c_13728,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13668,c_4029])).

tff(c_13769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4012,c_13728])).

tff(c_13770,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_14286,plain,(
    ! [A_388,B_389] : k5_xboole_0(k5_xboole_0(A_388,B_389),k2_xboole_0(A_388,B_389)) = k3_xboole_0(A_388,B_389) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16843,plain,(
    ! [A_454,B_455] : k5_xboole_0(A_454,k5_xboole_0(B_455,k2_xboole_0(A_454,B_455))) = k3_xboole_0(A_454,B_455) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_14286])).

tff(c_14063,plain,(
    ! [A_381,B_382,C_383] : k5_xboole_0(k5_xboole_0(A_381,B_382),C_383) = k5_xboole_0(A_381,k5_xboole_0(B_382,C_383)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14127,plain,(
    ! [A_15,C_383] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_383)) = k5_xboole_0(k1_xboole_0,C_383) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_14063])).

tff(c_14140,plain,(
    ! [A_15,C_383] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_383)) = C_383 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_14127])).

tff(c_16871,plain,(
    ! [B_455,A_454] : k5_xboole_0(B_455,k2_xboole_0(A_454,B_455)) = k5_xboole_0(A_454,k3_xboole_0(A_454,B_455)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16843,c_14140])).

tff(c_16956,plain,(
    ! [B_456,A_457] : k5_xboole_0(B_456,k2_xboole_0(A_457,B_456)) = k4_xboole_0(A_457,B_456) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16871])).

tff(c_17000,plain,(
    ! [B_456,A_457] : k5_xboole_0(B_456,k4_xboole_0(A_457,B_456)) = k2_xboole_0(A_457,B_456) ),
    inference(superposition,[status(thm),theory(equality)],[c_16956,c_14140])).

tff(c_14029,plain,(
    ! [B_377,A_378] :
      ( k3_xboole_0(B_377,k1_tarski(A_378)) = k1_tarski(A_378)
      | ~ r2_hidden(A_378,B_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22775,plain,(
    ! [B_517,A_518] :
      ( k5_xboole_0(B_517,k1_tarski(A_518)) = k4_xboole_0(B_517,k1_tarski(A_518))
      | ~ r2_hidden(A_518,B_517) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14029,c_8])).

tff(c_14141,plain,(
    ! [A_384,C_385] : k5_xboole_0(A_384,k5_xboole_0(A_384,C_385)) = C_385 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_14127])).

tff(c_14184,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14141])).

tff(c_22889,plain,(
    ! [A_518,B_517] :
      ( k5_xboole_0(k1_tarski(A_518),k4_xboole_0(B_517,k1_tarski(A_518))) = B_517
      | ~ r2_hidden(A_518,B_517) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22775,c_14184])).

tff(c_23040,plain,(
    ! [B_519,A_520] :
      ( k2_xboole_0(B_519,k1_tarski(A_520)) = B_519
      | ~ r2_hidden(A_520,B_519) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17000,c_22889])).

tff(c_13809,plain,(
    ! [A_348,B_349] : k3_tarski(k2_tarski(A_348,B_349)) = k2_xboole_0(A_348,B_349) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13846,plain,(
    ! [A_353,B_354] : k3_tarski(k2_tarski(A_353,B_354)) = k2_xboole_0(B_354,A_353) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_13809])).

tff(c_13852,plain,(
    ! [B_354,A_353] : k2_xboole_0(B_354,A_353) = k2_xboole_0(A_353,B_354) ),
    inference(superposition,[status(thm),theory(equality)],[c_13846,c_38])).

tff(c_17042,plain,(
    ! [A_353,B_354] : k5_xboole_0(A_353,k2_xboole_0(A_353,B_354)) = k4_xboole_0(B_354,A_353) ),
    inference(superposition,[status(thm),theory(equality)],[c_13852,c_16956])).

tff(c_23068,plain,(
    ! [B_519,A_520] :
      ( k5_xboole_0(B_519,B_519) = k4_xboole_0(k1_tarski(A_520),B_519)
      | ~ r2_hidden(A_520,B_519) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23040,c_17042])).

tff(c_23587,plain,(
    ! [A_526,B_527] :
      ( k4_xboole_0(k1_tarski(A_526),B_527) = k1_xboole_0
      | ~ r2_hidden(A_526,B_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_23068])).

tff(c_13771,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_13907,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13771,c_46])).

tff(c_23647,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23587,c_13907])).

tff(c_23685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13770,c_23647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.87/4.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/4.02  
% 9.87/4.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/4.02  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.87/4.02  
% 9.87/4.02  %Foreground sorts:
% 9.87/4.02  
% 9.87/4.02  
% 9.87/4.02  %Background operators:
% 9.87/4.02  
% 9.87/4.02  
% 9.87/4.02  %Foreground operators:
% 9.87/4.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.87/4.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.87/4.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.87/4.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.87/4.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.87/4.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.87/4.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.87/4.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.87/4.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.87/4.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.87/4.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.87/4.02  tff('#skF_2', type, '#skF_2': $i).
% 9.87/4.02  tff('#skF_3', type, '#skF_3': $i).
% 9.87/4.02  tff('#skF_1', type, '#skF_1': $i).
% 9.87/4.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.87/4.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.87/4.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.87/4.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.87/4.02  tff('#skF_4', type, '#skF_4': $i).
% 9.87/4.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.87/4.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.87/4.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.87/4.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.87/4.02  
% 10.01/4.05  tff(f_76, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 10.01/4.05  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.01/4.05  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.01/4.05  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.01/4.05  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.01/4.05  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.01/4.05  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.01/4.05  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.01/4.05  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.01/4.05  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.01/4.05  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.01/4.05  tff(f_71, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.01/4.05  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 10.01/4.05  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.01/4.05  tff(c_205, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 10.01/4.05  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.01/4.05  tff(c_111, plain, (![B_63, A_64]: (k5_xboole_0(B_63, A_64)=k5_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.01/4.05  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/4.05  tff(c_127, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_111, c_12])).
% 10.01/4.05  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/4.05  tff(c_500, plain, (![A_101, B_102, C_103]: (k5_xboole_0(k5_xboole_0(A_101, B_102), C_103)=k5_xboole_0(A_101, k5_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.01/4.05  tff(c_564, plain, (![A_15, C_103]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_103))=k5_xboole_0(k1_xboole_0, C_103))), inference(superposition, [status(thm), theory('equality')], [c_16, c_500])).
% 10.01/4.05  tff(c_578, plain, (![A_104, C_105]: (k5_xboole_0(A_104, k5_xboole_0(A_104, C_105))=C_105)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_564])).
% 10.01/4.05  tff(c_621, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_578])).
% 10.01/4.05  tff(c_643, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k5_xboole_0(B_107, A_106))=B_107)), inference(superposition, [status(thm), theory('equality')], [c_2, c_578])).
% 10.01/4.05  tff(c_670, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), B_2)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_621, c_643])).
% 10.01/4.05  tff(c_20, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/4.05  tff(c_242, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.01/4.05  tff(c_279, plain, (![B_73, A_74]: (k3_tarski(k2_tarski(B_73, A_74))=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_20, c_242])).
% 10.01/4.05  tff(c_38, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.01/4.05  tff(c_285, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_279, c_38])).
% 10.01/4.05  tff(c_52, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.01/4.05  tff(c_365, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 10.01/4.05  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.01/4.05  tff(c_722, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k2_xboole_0(A_108, B_109))=k3_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/4.05  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.01/4.05  tff(c_3599, plain, (![A_173, B_174]: (k5_xboole_0(A_173, k5_xboole_0(B_174, k2_xboole_0(A_173, B_174)))=k3_xboole_0(A_173, B_174))), inference(superposition, [status(thm), theory('equality')], [c_722, c_14])).
% 10.01/4.05  tff(c_577, plain, (![A_15, C_103]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_103))=C_103)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_564])).
% 10.01/4.05  tff(c_3639, plain, (![B_174, A_173]: (k5_xboole_0(B_174, k2_xboole_0(A_173, B_174))=k5_xboole_0(A_173, k3_xboole_0(A_173, B_174)))), inference(superposition, [status(thm), theory('equality')], [c_3599, c_577])).
% 10.01/4.05  tff(c_3733, plain, (![B_175, A_176]: (k5_xboole_0(B_175, k2_xboole_0(A_176, B_175))=k4_xboole_0(A_176, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3639])).
% 10.01/4.05  tff(c_3891, plain, (![A_178, B_179]: (k5_xboole_0(k2_xboole_0(A_178, B_179), k4_xboole_0(A_178, B_179))=B_179)), inference(superposition, [status(thm), theory('equality')], [c_3733, c_621])).
% 10.01/4.05  tff(c_3945, plain, (k5_xboole_0(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_365, c_3891])).
% 10.01/4.05  tff(c_3964, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_285, c_3945])).
% 10.01/4.05  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k2_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/4.05  tff(c_3975, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k1_tarski('#skF_3')), '#skF_4')=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3964, c_18])).
% 10.01/4.05  tff(c_3978, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_3975])).
% 10.01/4.05  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.01/4.05  tff(c_3998, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3978, c_10])).
% 10.01/4.05  tff(c_22, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.01/4.05  tff(c_340, plain, (![A_77, C_78, B_79]: (r2_hidden(A_77, C_78) | ~r1_tarski(k2_tarski(A_77, B_79), C_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.01/4.05  tff(c_353, plain, (![A_20, C_78]: (r2_hidden(A_20, C_78) | ~r1_tarski(k1_tarski(A_20), C_78))), inference(superposition, [status(thm), theory('equality')], [c_22, c_340])).
% 10.01/4.05  tff(c_4007, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_3998, c_353])).
% 10.01/4.05  tff(c_4011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_4007])).
% 10.01/4.05  tff(c_4012, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 10.01/4.05  tff(c_4367, plain, (![A_206, B_207]: (k5_xboole_0(k5_xboole_0(A_206, B_207), k2_xboole_0(A_206, B_207))=k3_xboole_0(A_206, B_207))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/4.05  tff(c_6924, plain, (![A_272, B_273]: (k5_xboole_0(A_272, k5_xboole_0(B_273, k2_xboole_0(A_272, B_273)))=k3_xboole_0(A_272, B_273))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4367])).
% 10.01/4.05  tff(c_4144, plain, (![A_199, B_200, C_201]: (k5_xboole_0(k5_xboole_0(A_199, B_200), C_201)=k5_xboole_0(A_199, k5_xboole_0(B_200, C_201)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.01/4.05  tff(c_4208, plain, (![A_15, C_201]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_201))=k5_xboole_0(k1_xboole_0, C_201))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4144])).
% 10.01/4.05  tff(c_4221, plain, (![A_15, C_201]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_201))=C_201)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_4208])).
% 10.01/4.05  tff(c_6952, plain, (![B_273, A_272]: (k5_xboole_0(B_273, k2_xboole_0(A_272, B_273))=k5_xboole_0(A_272, k3_xboole_0(A_272, B_273)))), inference(superposition, [status(thm), theory('equality')], [c_6924, c_4221])).
% 10.01/4.05  tff(c_7037, plain, (![B_274, A_275]: (k5_xboole_0(B_274, k2_xboole_0(A_275, B_274))=k4_xboole_0(A_275, B_274))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6952])).
% 10.01/4.05  tff(c_7081, plain, (![B_274, A_275]: (k5_xboole_0(B_274, k4_xboole_0(A_275, B_274))=k2_xboole_0(A_275, B_274))), inference(superposition, [status(thm), theory('equality')], [c_7037, c_4221])).
% 10.01/4.05  tff(c_4110, plain, (![B_195, A_196]: (k3_xboole_0(B_195, k1_tarski(A_196))=k1_tarski(A_196) | ~r2_hidden(A_196, B_195))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.01/4.05  tff(c_12856, plain, (![B_335, A_336]: (k5_xboole_0(B_335, k1_tarski(A_336))=k4_xboole_0(B_335, k1_tarski(A_336)) | ~r2_hidden(A_336, B_335))), inference(superposition, [status(thm), theory('equality')], [c_4110, c_8])).
% 10.01/4.05  tff(c_4222, plain, (![A_202, C_203]: (k5_xboole_0(A_202, k5_xboole_0(A_202, C_203))=C_203)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_4208])).
% 10.01/4.05  tff(c_4265, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4222])).
% 10.01/4.05  tff(c_12970, plain, (![A_336, B_335]: (k5_xboole_0(k1_tarski(A_336), k4_xboole_0(B_335, k1_tarski(A_336)))=B_335 | ~r2_hidden(A_336, B_335))), inference(superposition, [status(thm), theory('equality')], [c_12856, c_4265])).
% 10.01/4.05  tff(c_13121, plain, (![B_337, A_338]: (k2_xboole_0(B_337, k1_tarski(A_338))=B_337 | ~r2_hidden(A_338, B_337))), inference(demodulation, [status(thm), theory('equality')], [c_7081, c_12970])).
% 10.01/4.05  tff(c_7123, plain, (![A_74, B_73]: (k5_xboole_0(A_74, k2_xboole_0(A_74, B_73))=k4_xboole_0(B_73, A_74))), inference(superposition, [status(thm), theory('equality')], [c_285, c_7037])).
% 10.01/4.05  tff(c_13149, plain, (![B_337, A_338]: (k5_xboole_0(B_337, B_337)=k4_xboole_0(k1_tarski(A_338), B_337) | ~r2_hidden(A_338, B_337))), inference(superposition, [status(thm), theory('equality')], [c_13121, c_7123])).
% 10.01/4.05  tff(c_13668, plain, (![A_344, B_345]: (k4_xboole_0(k1_tarski(A_344), B_345)=k1_xboole_0 | ~r2_hidden(A_344, B_345))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_13149])).
% 10.01/4.05  tff(c_4013, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 10.01/4.05  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.01/4.05  tff(c_4029, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4013, c_50])).
% 10.01/4.05  tff(c_13728, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13668, c_4029])).
% 10.01/4.05  tff(c_13769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4012, c_13728])).
% 10.01/4.05  tff(c_13770, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 10.01/4.05  tff(c_14286, plain, (![A_388, B_389]: (k5_xboole_0(k5_xboole_0(A_388, B_389), k2_xboole_0(A_388, B_389))=k3_xboole_0(A_388, B_389))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/4.05  tff(c_16843, plain, (![A_454, B_455]: (k5_xboole_0(A_454, k5_xboole_0(B_455, k2_xboole_0(A_454, B_455)))=k3_xboole_0(A_454, B_455))), inference(superposition, [status(thm), theory('equality')], [c_14, c_14286])).
% 10.01/4.05  tff(c_14063, plain, (![A_381, B_382, C_383]: (k5_xboole_0(k5_xboole_0(A_381, B_382), C_383)=k5_xboole_0(A_381, k5_xboole_0(B_382, C_383)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.01/4.05  tff(c_14127, plain, (![A_15, C_383]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_383))=k5_xboole_0(k1_xboole_0, C_383))), inference(superposition, [status(thm), theory('equality')], [c_16, c_14063])).
% 10.01/4.05  tff(c_14140, plain, (![A_15, C_383]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_383))=C_383)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_14127])).
% 10.01/4.05  tff(c_16871, plain, (![B_455, A_454]: (k5_xboole_0(B_455, k2_xboole_0(A_454, B_455))=k5_xboole_0(A_454, k3_xboole_0(A_454, B_455)))), inference(superposition, [status(thm), theory('equality')], [c_16843, c_14140])).
% 10.01/4.05  tff(c_16956, plain, (![B_456, A_457]: (k5_xboole_0(B_456, k2_xboole_0(A_457, B_456))=k4_xboole_0(A_457, B_456))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16871])).
% 10.01/4.05  tff(c_17000, plain, (![B_456, A_457]: (k5_xboole_0(B_456, k4_xboole_0(A_457, B_456))=k2_xboole_0(A_457, B_456))), inference(superposition, [status(thm), theory('equality')], [c_16956, c_14140])).
% 10.01/4.05  tff(c_14029, plain, (![B_377, A_378]: (k3_xboole_0(B_377, k1_tarski(A_378))=k1_tarski(A_378) | ~r2_hidden(A_378, B_377))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.01/4.05  tff(c_22775, plain, (![B_517, A_518]: (k5_xboole_0(B_517, k1_tarski(A_518))=k4_xboole_0(B_517, k1_tarski(A_518)) | ~r2_hidden(A_518, B_517))), inference(superposition, [status(thm), theory('equality')], [c_14029, c_8])).
% 10.01/4.05  tff(c_14141, plain, (![A_384, C_385]: (k5_xboole_0(A_384, k5_xboole_0(A_384, C_385))=C_385)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_14127])).
% 10.01/4.05  tff(c_14184, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_14141])).
% 10.01/4.05  tff(c_22889, plain, (![A_518, B_517]: (k5_xboole_0(k1_tarski(A_518), k4_xboole_0(B_517, k1_tarski(A_518)))=B_517 | ~r2_hidden(A_518, B_517))), inference(superposition, [status(thm), theory('equality')], [c_22775, c_14184])).
% 10.01/4.05  tff(c_23040, plain, (![B_519, A_520]: (k2_xboole_0(B_519, k1_tarski(A_520))=B_519 | ~r2_hidden(A_520, B_519))), inference(demodulation, [status(thm), theory('equality')], [c_17000, c_22889])).
% 10.01/4.05  tff(c_13809, plain, (![A_348, B_349]: (k3_tarski(k2_tarski(A_348, B_349))=k2_xboole_0(A_348, B_349))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.01/4.05  tff(c_13846, plain, (![A_353, B_354]: (k3_tarski(k2_tarski(A_353, B_354))=k2_xboole_0(B_354, A_353))), inference(superposition, [status(thm), theory('equality')], [c_20, c_13809])).
% 10.01/4.05  tff(c_13852, plain, (![B_354, A_353]: (k2_xboole_0(B_354, A_353)=k2_xboole_0(A_353, B_354))), inference(superposition, [status(thm), theory('equality')], [c_13846, c_38])).
% 10.01/4.05  tff(c_17042, plain, (![A_353, B_354]: (k5_xboole_0(A_353, k2_xboole_0(A_353, B_354))=k4_xboole_0(B_354, A_353))), inference(superposition, [status(thm), theory('equality')], [c_13852, c_16956])).
% 10.01/4.05  tff(c_23068, plain, (![B_519, A_520]: (k5_xboole_0(B_519, B_519)=k4_xboole_0(k1_tarski(A_520), B_519) | ~r2_hidden(A_520, B_519))), inference(superposition, [status(thm), theory('equality')], [c_23040, c_17042])).
% 10.01/4.05  tff(c_23587, plain, (![A_526, B_527]: (k4_xboole_0(k1_tarski(A_526), B_527)=k1_xboole_0 | ~r2_hidden(A_526, B_527))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_23068])).
% 10.01/4.05  tff(c_13771, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 10.01/4.05  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.01/4.05  tff(c_13907, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13771, c_46])).
% 10.01/4.05  tff(c_23647, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_23587, c_13907])).
% 10.01/4.05  tff(c_23685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13770, c_23647])).
% 10.01/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/4.05  
% 10.01/4.05  Inference rules
% 10.01/4.05  ----------------------
% 10.01/4.05  #Ref     : 0
% 10.01/4.05  #Sup     : 5861
% 10.01/4.05  #Fact    : 0
% 10.01/4.05  #Define  : 0
% 10.01/4.05  #Split   : 2
% 10.01/4.05  #Chain   : 0
% 10.01/4.05  #Close   : 0
% 10.01/4.05  
% 10.01/4.05  Ordering : KBO
% 10.01/4.05  
% 10.01/4.05  Simplification rules
% 10.01/4.05  ----------------------
% 10.01/4.05  #Subsume      : 399
% 10.01/4.05  #Demod        : 5638
% 10.01/4.05  #Tautology    : 3109
% 10.01/4.05  #SimpNegUnit  : 2
% 10.01/4.05  #BackRed      : 3
% 10.01/4.05  
% 10.01/4.05  #Partial instantiations: 0
% 10.01/4.05  #Strategies tried      : 1
% 10.01/4.05  
% 10.01/4.05  Timing (in seconds)
% 10.01/4.05  ----------------------
% 10.01/4.05  Preprocessing        : 0.32
% 10.01/4.05  Parsing              : 0.17
% 10.01/4.05  CNF conversion       : 0.02
% 10.01/4.05  Main loop            : 2.96
% 10.01/4.05  Inferencing          : 0.67
% 10.01/4.05  Reduction            : 1.66
% 10.01/4.05  Demodulation         : 1.48
% 10.01/4.05  BG Simplification    : 0.09
% 10.01/4.05  Subsumption          : 0.40
% 10.01/4.05  Abstraction          : 0.14
% 10.01/4.05  MUC search           : 0.00
% 10.01/4.05  Cooper               : 0.00
% 10.01/4.05  Total                : 3.32
% 10.01/4.05  Index Insertion      : 0.00
% 10.01/4.05  Index Deletion       : 0.00
% 10.01/4.05  Index Matching       : 0.00
% 10.01/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
