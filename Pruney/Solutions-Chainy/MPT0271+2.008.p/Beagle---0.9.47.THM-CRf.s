%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:02 EST 2020

% Result     : Theorem 10.24s
% Output     : CNFRefutation 10.24s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 321 expanded)
%              Number of leaves         :   34 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 328 expanded)
%              Number of equality atoms :   96 ( 287 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_78,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_48,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_146,plain,(
    ! [B_65,A_66] : k5_xboole_0(B_65,A_66) = k5_xboole_0(A_66,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_66] : k5_xboole_0(k1_xboole_0,A_66) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_12])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_759,plain,(
    ! [A_101,B_102,C_103] : k5_xboole_0(k5_xboole_0(A_101,B_102),C_103) = k5_xboole_0(A_101,k5_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_858,plain,(
    ! [A_16,C_103] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_103)) = k5_xboole_0(k1_xboole_0,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_759])).

tff(c_875,plain,(
    ! [A_16,C_103] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_103)) = C_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_858])).

tff(c_52,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_341,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_24,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_244,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_281,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_244])).

tff(c_44,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_287,plain,(
    ! [B_74,A_73] : k2_xboole_0(B_74,A_73) = k2_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_876,plain,(
    ! [A_104,C_105] : k5_xboole_0(A_104,k5_xboole_0(A_104,C_105)) = C_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_858])).

tff(c_931,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_876])).

tff(c_14,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_547,plain,(
    ! [A_95,B_96] : k5_xboole_0(k5_xboole_0(A_95,B_96),k2_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2798,plain,(
    ! [A_155,B_156] : k5_xboole_0(k2_xboole_0(A_155,B_156),k5_xboole_0(A_155,B_156)) = k3_xboole_0(A_155,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_547])).

tff(c_2926,plain,(
    ! [A_11,B_12] : k5_xboole_0(k2_xboole_0(A_11,B_12),k5_xboole_0(A_11,k2_xboole_0(A_11,B_12))) = k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2798])).

tff(c_2977,plain,(
    ! [A_157,B_158] : k3_xboole_0(A_157,k2_xboole_0(A_157,B_158)) = A_157 ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_2926])).

tff(c_3027,plain,(
    ! [A_73,B_74] : k3_xboole_0(A_73,k2_xboole_0(B_74,A_73)) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_2977])).

tff(c_347,plain,(
    ! [A_77,B_78] : k2_xboole_0(A_77,k2_xboole_0(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_362,plain,(
    ! [A_73,B_74] : k2_xboole_0(A_73,k2_xboole_0(B_74,A_73)) = k2_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_347])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k2_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4023,plain,(
    ! [A_173,B_174] : k5_xboole_0(A_173,k5_xboole_0(B_174,k2_xboole_0(A_173,B_174))) = k3_xboole_0(A_173,B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_22])).

tff(c_4078,plain,(
    ! [B_174,A_173] : k5_xboole_0(B_174,k2_xboole_0(A_173,B_174)) = k5_xboole_0(A_173,k3_xboole_0(A_173,B_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4023,c_875])).

tff(c_4192,plain,(
    ! [B_175,A_176] : k5_xboole_0(B_175,k2_xboole_0(A_176,B_175)) = k4_xboole_0(A_176,B_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4078])).

tff(c_589,plain,(
    ! [A_95,B_96] : k5_xboole_0(k2_xboole_0(A_95,B_96),k5_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_547])).

tff(c_4210,plain,(
    ! [B_175,A_176] : k5_xboole_0(k2_xboole_0(B_175,k2_xboole_0(A_176,B_175)),k4_xboole_0(A_176,B_175)) = k3_xboole_0(B_175,k2_xboole_0(A_176,B_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4192,c_589])).

tff(c_4320,plain,(
    ! [B_177,A_178] : k5_xboole_0(k2_xboole_0(B_177,A_178),k4_xboole_0(A_178,B_177)) = B_177 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3027,c_362,c_4210])).

tff(c_4422,plain,(
    k5_xboole_0(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_4320])).

tff(c_4511,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4422,c_12])).

tff(c_4569,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0('#skF_4',k1_tarski('#skF_3'))) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4511,c_589])).

tff(c_4587,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_4569])).

tff(c_40,plain,(
    ! [B_52,A_51] :
      ( r2_hidden(B_52,A_51)
      | k3_xboole_0(A_51,k1_tarski(B_52)) != k1_tarski(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4619,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4587,c_40])).

tff(c_4633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_4619])).

tff(c_4634,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5091,plain,(
    ! [A_202,B_203,C_204] : k5_xboole_0(k5_xboole_0(A_202,B_203),C_204) = k5_xboole_0(A_202,k5_xboole_0(B_203,C_204)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9634,plain,(
    ! [A_294,B_295] : k5_xboole_0(A_294,k5_xboole_0(B_295,k2_xboole_0(A_294,B_295))) = k3_xboole_0(A_294,B_295) ),
    inference(superposition,[status(thm),theory(equality)],[c_5091,c_22])).

tff(c_5171,plain,(
    ! [A_16,C_204] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_204)) = k5_xboole_0(k1_xboole_0,C_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5091])).

tff(c_5184,plain,(
    ! [A_16,C_204] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_204)) = C_204 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_5171])).

tff(c_9714,plain,(
    ! [B_295,A_294] : k5_xboole_0(B_295,k2_xboole_0(A_294,B_295)) = k5_xboole_0(A_294,k3_xboole_0(A_294,B_295)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9634,c_5184])).

tff(c_9837,plain,(
    ! [B_296,A_297] : k5_xboole_0(B_296,k2_xboole_0(A_297,B_296)) = k4_xboole_0(A_297,B_296) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9714])).

tff(c_9910,plain,(
    ! [B_296,A_297] : k5_xboole_0(B_296,k4_xboole_0(A_297,B_296)) = k2_xboole_0(A_297,B_296) ),
    inference(superposition,[status(thm),theory(equality)],[c_9837,c_5184])).

tff(c_4782,plain,(
    ! [B_190,A_191] :
      ( k3_xboole_0(B_190,k1_tarski(A_191)) = k1_tarski(A_191)
      | ~ r2_hidden(A_191,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_11514,plain,(
    ! [B_322,A_323] :
      ( k5_xboole_0(B_322,k1_tarski(A_323)) = k4_xboole_0(B_322,k1_tarski(A_323))
      | ~ r2_hidden(A_323,B_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4782,c_8])).

tff(c_5258,plain,(
    ! [A_211,C_212] : k5_xboole_0(A_211,k5_xboole_0(A_211,C_212)) = C_212 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_5171])).

tff(c_5310,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5258])).

tff(c_11604,plain,(
    ! [A_323,B_322] :
      ( k5_xboole_0(k1_tarski(A_323),k4_xboole_0(B_322,k1_tarski(A_323))) = B_322
      | ~ r2_hidden(A_323,B_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11514,c_5310])).

tff(c_11831,plain,(
    ! [B_328,A_329] :
      ( k2_xboole_0(B_328,k1_tarski(A_329)) = B_328
      | ~ r2_hidden(A_329,B_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9910,c_11604])).

tff(c_9959,plain,(
    ! [B_74,A_73] : k5_xboole_0(B_74,k2_xboole_0(B_74,A_73)) = k4_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_9837])).

tff(c_11837,plain,(
    ! [B_328,A_329] :
      ( k5_xboole_0(B_328,B_328) = k4_xboole_0(k1_tarski(A_329),B_328)
      | ~ r2_hidden(A_329,B_328) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11831,c_9959])).

tff(c_14732,plain,(
    ! [A_358,B_359] :
      ( k4_xboole_0(k1_tarski(A_358),B_359) = k1_xboole_0
      | ~ r2_hidden(A_358,B_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11837])).

tff(c_4635,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4780,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4635,c_50])).

tff(c_14821,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14732,c_4780])).

tff(c_14889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4634,c_14821])).

tff(c_14890,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_42,plain,(
    ! [B_54,A_53] :
      ( k3_xboole_0(B_54,k1_tarski(A_53)) = k1_tarski(A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_15348,plain,(
    ! [A_391,B_392,C_393] : k5_xboole_0(k5_xboole_0(A_391,B_392),C_393) = k5_xboole_0(A_391,k5_xboole_0(B_392,C_393)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15447,plain,(
    ! [A_16,C_393] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_393)) = k5_xboole_0(k1_xboole_0,C_393) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_15348])).

tff(c_15465,plain,(
    ! [A_394,C_395] : k5_xboole_0(A_394,k5_xboole_0(A_394,C_395)) = C_395 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_15447])).

tff(c_15510,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15465])).

tff(c_14893,plain,(
    ! [A_360,B_361] : k3_tarski(k2_tarski(A_360,B_361)) = k2_xboole_0(A_360,B_361) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14933,plain,(
    ! [A_365,B_366] : k3_tarski(k2_tarski(A_365,B_366)) = k2_xboole_0(B_366,A_365) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_14893])).

tff(c_14939,plain,(
    ! [B_366,A_365] : k2_xboole_0(B_366,A_365) = k2_xboole_0(A_365,B_366) ),
    inference(superposition,[status(thm),theory(equality)],[c_14933,c_44])).

tff(c_16741,plain,(
    ! [A_443,B_444] : k5_xboole_0(A_443,k5_xboole_0(B_444,k2_xboole_0(A_443,B_444))) = k3_xboole_0(A_443,B_444) ),
    inference(superposition,[status(thm),theory(equality)],[c_15348,c_22])).

tff(c_15464,plain,(
    ! [A_16,C_393] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_393)) = C_393 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_15447])).

tff(c_16766,plain,(
    ! [B_444,A_443] : k5_xboole_0(B_444,k2_xboole_0(A_443,B_444)) = k5_xboole_0(A_443,k3_xboole_0(A_443,B_444)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16741,c_15464])).

tff(c_17388,plain,(
    ! [B_457,A_458] : k5_xboole_0(B_457,k2_xboole_0(A_458,B_457)) = k4_xboole_0(A_458,B_457) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16766])).

tff(c_17465,plain,(
    ! [A_365,B_366] : k5_xboole_0(A_365,k2_xboole_0(A_365,B_366)) = k4_xboole_0(B_366,A_365) ),
    inference(superposition,[status(thm),theory(equality)],[c_14939,c_17388])).

tff(c_15430,plain,(
    ! [B_2,A_391,B_392] : k5_xboole_0(B_2,k5_xboole_0(A_391,B_392)) = k5_xboole_0(A_391,k5_xboole_0(B_392,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15348])).

tff(c_15190,plain,(
    ! [A_386,B_387] : k5_xboole_0(k5_xboole_0(A_386,B_387),k2_xboole_0(A_386,B_387)) = k3_xboole_0(A_386,B_387) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_23250,plain,(
    ! [B_526,A_527] : k5_xboole_0(k5_xboole_0(B_526,A_527),k2_xboole_0(A_527,B_526)) = k3_xboole_0(A_527,B_526) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15190])).

tff(c_17896,plain,(
    ! [B_467,A_468,B_469] : k5_xboole_0(B_467,k5_xboole_0(A_468,B_469)) = k5_xboole_0(A_468,k5_xboole_0(B_469,B_467)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15348])).

tff(c_18526,plain,(
    ! [A_472,B_473] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_472,B_473)) = k5_xboole_0(B_473,A_472) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_17896])).

tff(c_15523,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15465])).

tff(c_18562,plain,(
    ! [A_472,B_473] : k5_xboole_0(k5_xboole_0(A_472,B_473),k5_xboole_0(B_473,A_472)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18526,c_15523])).

tff(c_23289,plain,(
    ! [A_527,B_526] : k5_xboole_0(k5_xboole_0(k2_xboole_0(A_527,B_526),k5_xboole_0(B_526,A_527)),k3_xboole_0(A_527,B_526)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_23250,c_18562])).

tff(c_23576,plain,(
    ! [A_528,B_529] : k5_xboole_0(k3_xboole_0(A_528,B_529),k3_xboole_0(B_529,A_528)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15510,c_17465,c_2,c_15430,c_23289])).

tff(c_23745,plain,(
    ! [A_53,B_54] :
      ( k5_xboole_0(k1_tarski(A_53),k3_xboole_0(k1_tarski(A_53),B_54)) = k1_xboole_0
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_23576])).

tff(c_25782,plain,(
    ! [A_554,B_555] :
      ( k4_xboole_0(k1_tarski(A_554),B_555) = k1_xboole_0
      | ~ r2_hidden(A_554,B_555) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_23745])).

tff(c_14891,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14995,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14891,c_46])).

tff(c_25871,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25782,c_14995])).

tff(c_25929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14890,c_25871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:11:42 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.24/4.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.24/4.11  
% 10.24/4.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.24/4.11  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.24/4.11  
% 10.24/4.11  %Foreground sorts:
% 10.24/4.11  
% 10.24/4.11  
% 10.24/4.11  %Background operators:
% 10.24/4.11  
% 10.24/4.11  
% 10.24/4.11  %Foreground operators:
% 10.24/4.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.24/4.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.24/4.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.24/4.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.24/4.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.24/4.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.24/4.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.24/4.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.24/4.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.24/4.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.24/4.11  tff('#skF_2', type, '#skF_2': $i).
% 10.24/4.11  tff('#skF_3', type, '#skF_3': $i).
% 10.24/4.11  tff('#skF_1', type, '#skF_1': $i).
% 10.24/4.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.24/4.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.24/4.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.24/4.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.24/4.11  tff('#skF_4', type, '#skF_4': $i).
% 10.24/4.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.24/4.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.24/4.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.24/4.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.24/4.11  
% 10.24/4.13  tff(f_78, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 10.24/4.13  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.24/4.13  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.24/4.13  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.24/4.13  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.24/4.13  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.24/4.13  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.24/4.13  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 10.24/4.13  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.24/4.13  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.24/4.13  tff(f_67, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 10.24/4.13  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 10.24/4.13  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.24/4.13  tff(c_240, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 10.24/4.13  tff(c_146, plain, (![B_65, A_66]: (k5_xboole_0(B_65, A_66)=k5_xboole_0(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.24/4.13  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.24/4.13  tff(c_162, plain, (![A_66]: (k5_xboole_0(k1_xboole_0, A_66)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_146, c_12])).
% 10.24/4.13  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.24/4.13  tff(c_759, plain, (![A_101, B_102, C_103]: (k5_xboole_0(k5_xboole_0(A_101, B_102), C_103)=k5_xboole_0(A_101, k5_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.24/4.13  tff(c_858, plain, (![A_16, C_103]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_103))=k5_xboole_0(k1_xboole_0, C_103))), inference(superposition, [status(thm), theory('equality')], [c_18, c_759])).
% 10.24/4.13  tff(c_875, plain, (![A_16, C_103]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_103))=C_103)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_858])).
% 10.24/4.13  tff(c_52, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.24/4.13  tff(c_341, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 10.24/4.13  tff(c_24, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.24/4.13  tff(c_244, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.24/4.13  tff(c_281, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_24, c_244])).
% 10.24/4.13  tff(c_44, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.24/4.13  tff(c_287, plain, (![B_74, A_73]: (k2_xboole_0(B_74, A_73)=k2_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_281, c_44])).
% 10.24/4.13  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.24/4.13  tff(c_876, plain, (![A_104, C_105]: (k5_xboole_0(A_104, k5_xboole_0(A_104, C_105))=C_105)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_858])).
% 10.24/4.13  tff(c_931, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_876])).
% 10.24/4.13  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.24/4.13  tff(c_547, plain, (![A_95, B_96]: (k5_xboole_0(k5_xboole_0(A_95, B_96), k2_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.24/4.13  tff(c_2798, plain, (![A_155, B_156]: (k5_xboole_0(k2_xboole_0(A_155, B_156), k5_xboole_0(A_155, B_156))=k3_xboole_0(A_155, B_156))), inference(superposition, [status(thm), theory('equality')], [c_2, c_547])).
% 10.24/4.13  tff(c_2926, plain, (![A_11, B_12]: (k5_xboole_0(k2_xboole_0(A_11, B_12), k5_xboole_0(A_11, k2_xboole_0(A_11, B_12)))=k3_xboole_0(A_11, k2_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2798])).
% 10.24/4.13  tff(c_2977, plain, (![A_157, B_158]: (k3_xboole_0(A_157, k2_xboole_0(A_157, B_158))=A_157)), inference(demodulation, [status(thm), theory('equality')], [c_931, c_2926])).
% 10.24/4.13  tff(c_3027, plain, (![A_73, B_74]: (k3_xboole_0(A_73, k2_xboole_0(B_74, A_73))=A_73)), inference(superposition, [status(thm), theory('equality')], [c_287, c_2977])).
% 10.24/4.13  tff(c_347, plain, (![A_77, B_78]: (k2_xboole_0(A_77, k2_xboole_0(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.24/4.13  tff(c_362, plain, (![A_73, B_74]: (k2_xboole_0(A_73, k2_xboole_0(B_74, A_73))=k2_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_287, c_347])).
% 10.24/4.13  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.24/4.13  tff(c_22, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k2_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.24/4.13  tff(c_4023, plain, (![A_173, B_174]: (k5_xboole_0(A_173, k5_xboole_0(B_174, k2_xboole_0(A_173, B_174)))=k3_xboole_0(A_173, B_174))), inference(superposition, [status(thm), theory('equality')], [c_759, c_22])).
% 10.24/4.13  tff(c_4078, plain, (![B_174, A_173]: (k5_xboole_0(B_174, k2_xboole_0(A_173, B_174))=k5_xboole_0(A_173, k3_xboole_0(A_173, B_174)))), inference(superposition, [status(thm), theory('equality')], [c_4023, c_875])).
% 10.24/4.13  tff(c_4192, plain, (![B_175, A_176]: (k5_xboole_0(B_175, k2_xboole_0(A_176, B_175))=k4_xboole_0(A_176, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4078])).
% 10.24/4.13  tff(c_589, plain, (![A_95, B_96]: (k5_xboole_0(k2_xboole_0(A_95, B_96), k5_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_2, c_547])).
% 10.24/4.13  tff(c_4210, plain, (![B_175, A_176]: (k5_xboole_0(k2_xboole_0(B_175, k2_xboole_0(A_176, B_175)), k4_xboole_0(A_176, B_175))=k3_xboole_0(B_175, k2_xboole_0(A_176, B_175)))), inference(superposition, [status(thm), theory('equality')], [c_4192, c_589])).
% 10.24/4.13  tff(c_4320, plain, (![B_177, A_178]: (k5_xboole_0(k2_xboole_0(B_177, A_178), k4_xboole_0(A_178, B_177))=B_177)), inference(demodulation, [status(thm), theory('equality')], [c_3027, c_362, c_4210])).
% 10.24/4.13  tff(c_4422, plain, (k5_xboole_0(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_341, c_4320])).
% 10.24/4.13  tff(c_4511, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4422, c_12])).
% 10.24/4.13  tff(c_4569, plain, (k5_xboole_0('#skF_4', k5_xboole_0('#skF_4', k1_tarski('#skF_3')))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4511, c_589])).
% 10.24/4.13  tff(c_4587, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_875, c_4569])).
% 10.24/4.13  tff(c_40, plain, (![B_52, A_51]: (r2_hidden(B_52, A_51) | k3_xboole_0(A_51, k1_tarski(B_52))!=k1_tarski(B_52))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.24/4.13  tff(c_4619, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4587, c_40])).
% 10.24/4.13  tff(c_4633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_4619])).
% 10.24/4.13  tff(c_4634, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 10.24/4.13  tff(c_5091, plain, (![A_202, B_203, C_204]: (k5_xboole_0(k5_xboole_0(A_202, B_203), C_204)=k5_xboole_0(A_202, k5_xboole_0(B_203, C_204)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.24/4.13  tff(c_9634, plain, (![A_294, B_295]: (k5_xboole_0(A_294, k5_xboole_0(B_295, k2_xboole_0(A_294, B_295)))=k3_xboole_0(A_294, B_295))), inference(superposition, [status(thm), theory('equality')], [c_5091, c_22])).
% 10.24/4.13  tff(c_5171, plain, (![A_16, C_204]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_204))=k5_xboole_0(k1_xboole_0, C_204))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5091])).
% 10.24/4.13  tff(c_5184, plain, (![A_16, C_204]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_204))=C_204)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_5171])).
% 10.24/4.13  tff(c_9714, plain, (![B_295, A_294]: (k5_xboole_0(B_295, k2_xboole_0(A_294, B_295))=k5_xboole_0(A_294, k3_xboole_0(A_294, B_295)))), inference(superposition, [status(thm), theory('equality')], [c_9634, c_5184])).
% 10.24/4.13  tff(c_9837, plain, (![B_296, A_297]: (k5_xboole_0(B_296, k2_xboole_0(A_297, B_296))=k4_xboole_0(A_297, B_296))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_9714])).
% 10.24/4.13  tff(c_9910, plain, (![B_296, A_297]: (k5_xboole_0(B_296, k4_xboole_0(A_297, B_296))=k2_xboole_0(A_297, B_296))), inference(superposition, [status(thm), theory('equality')], [c_9837, c_5184])).
% 10.24/4.13  tff(c_4782, plain, (![B_190, A_191]: (k3_xboole_0(B_190, k1_tarski(A_191))=k1_tarski(A_191) | ~r2_hidden(A_191, B_190))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.24/4.13  tff(c_11514, plain, (![B_322, A_323]: (k5_xboole_0(B_322, k1_tarski(A_323))=k4_xboole_0(B_322, k1_tarski(A_323)) | ~r2_hidden(A_323, B_322))), inference(superposition, [status(thm), theory('equality')], [c_4782, c_8])).
% 10.24/4.13  tff(c_5258, plain, (![A_211, C_212]: (k5_xboole_0(A_211, k5_xboole_0(A_211, C_212))=C_212)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_5171])).
% 10.24/4.13  tff(c_5310, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5258])).
% 10.24/4.13  tff(c_11604, plain, (![A_323, B_322]: (k5_xboole_0(k1_tarski(A_323), k4_xboole_0(B_322, k1_tarski(A_323)))=B_322 | ~r2_hidden(A_323, B_322))), inference(superposition, [status(thm), theory('equality')], [c_11514, c_5310])).
% 10.24/4.13  tff(c_11831, plain, (![B_328, A_329]: (k2_xboole_0(B_328, k1_tarski(A_329))=B_328 | ~r2_hidden(A_329, B_328))), inference(demodulation, [status(thm), theory('equality')], [c_9910, c_11604])).
% 10.24/4.13  tff(c_9959, plain, (![B_74, A_73]: (k5_xboole_0(B_74, k2_xboole_0(B_74, A_73))=k4_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_287, c_9837])).
% 10.24/4.13  tff(c_11837, plain, (![B_328, A_329]: (k5_xboole_0(B_328, B_328)=k4_xboole_0(k1_tarski(A_329), B_328) | ~r2_hidden(A_329, B_328))), inference(superposition, [status(thm), theory('equality')], [c_11831, c_9959])).
% 10.24/4.13  tff(c_14732, plain, (![A_358, B_359]: (k4_xboole_0(k1_tarski(A_358), B_359)=k1_xboole_0 | ~r2_hidden(A_358, B_359))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11837])).
% 10.24/4.13  tff(c_4635, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 10.24/4.13  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.24/4.13  tff(c_4780, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4635, c_50])).
% 10.24/4.13  tff(c_14821, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14732, c_4780])).
% 10.24/4.13  tff(c_14889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4634, c_14821])).
% 10.24/4.13  tff(c_14890, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 10.24/4.13  tff(c_42, plain, (![B_54, A_53]: (k3_xboole_0(B_54, k1_tarski(A_53))=k1_tarski(A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.24/4.13  tff(c_15348, plain, (![A_391, B_392, C_393]: (k5_xboole_0(k5_xboole_0(A_391, B_392), C_393)=k5_xboole_0(A_391, k5_xboole_0(B_392, C_393)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.24/4.13  tff(c_15447, plain, (![A_16, C_393]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_393))=k5_xboole_0(k1_xboole_0, C_393))), inference(superposition, [status(thm), theory('equality')], [c_18, c_15348])).
% 10.24/4.13  tff(c_15465, plain, (![A_394, C_395]: (k5_xboole_0(A_394, k5_xboole_0(A_394, C_395))=C_395)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_15447])).
% 10.24/4.13  tff(c_15510, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_15465])).
% 10.24/4.13  tff(c_14893, plain, (![A_360, B_361]: (k3_tarski(k2_tarski(A_360, B_361))=k2_xboole_0(A_360, B_361))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.24/4.13  tff(c_14933, plain, (![A_365, B_366]: (k3_tarski(k2_tarski(A_365, B_366))=k2_xboole_0(B_366, A_365))), inference(superposition, [status(thm), theory('equality')], [c_24, c_14893])).
% 10.24/4.13  tff(c_14939, plain, (![B_366, A_365]: (k2_xboole_0(B_366, A_365)=k2_xboole_0(A_365, B_366))), inference(superposition, [status(thm), theory('equality')], [c_14933, c_44])).
% 10.24/4.13  tff(c_16741, plain, (![A_443, B_444]: (k5_xboole_0(A_443, k5_xboole_0(B_444, k2_xboole_0(A_443, B_444)))=k3_xboole_0(A_443, B_444))), inference(superposition, [status(thm), theory('equality')], [c_15348, c_22])).
% 10.24/4.13  tff(c_15464, plain, (![A_16, C_393]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_393))=C_393)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_15447])).
% 10.24/4.13  tff(c_16766, plain, (![B_444, A_443]: (k5_xboole_0(B_444, k2_xboole_0(A_443, B_444))=k5_xboole_0(A_443, k3_xboole_0(A_443, B_444)))), inference(superposition, [status(thm), theory('equality')], [c_16741, c_15464])).
% 10.24/4.13  tff(c_17388, plain, (![B_457, A_458]: (k5_xboole_0(B_457, k2_xboole_0(A_458, B_457))=k4_xboole_0(A_458, B_457))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16766])).
% 10.24/4.13  tff(c_17465, plain, (![A_365, B_366]: (k5_xboole_0(A_365, k2_xboole_0(A_365, B_366))=k4_xboole_0(B_366, A_365))), inference(superposition, [status(thm), theory('equality')], [c_14939, c_17388])).
% 10.24/4.13  tff(c_15430, plain, (![B_2, A_391, B_392]: (k5_xboole_0(B_2, k5_xboole_0(A_391, B_392))=k5_xboole_0(A_391, k5_xboole_0(B_392, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15348])).
% 10.24/4.13  tff(c_15190, plain, (![A_386, B_387]: (k5_xboole_0(k5_xboole_0(A_386, B_387), k2_xboole_0(A_386, B_387))=k3_xboole_0(A_386, B_387))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.24/4.13  tff(c_23250, plain, (![B_526, A_527]: (k5_xboole_0(k5_xboole_0(B_526, A_527), k2_xboole_0(A_527, B_526))=k3_xboole_0(A_527, B_526))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15190])).
% 10.24/4.13  tff(c_17896, plain, (![B_467, A_468, B_469]: (k5_xboole_0(B_467, k5_xboole_0(A_468, B_469))=k5_xboole_0(A_468, k5_xboole_0(B_469, B_467)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15348])).
% 10.24/4.13  tff(c_18526, plain, (![A_472, B_473]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_472, B_473))=k5_xboole_0(B_473, A_472))), inference(superposition, [status(thm), theory('equality')], [c_162, c_17896])).
% 10.24/4.13  tff(c_15523, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_15465])).
% 10.24/4.13  tff(c_18562, plain, (![A_472, B_473]: (k5_xboole_0(k5_xboole_0(A_472, B_473), k5_xboole_0(B_473, A_472))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18526, c_15523])).
% 10.24/4.13  tff(c_23289, plain, (![A_527, B_526]: (k5_xboole_0(k5_xboole_0(k2_xboole_0(A_527, B_526), k5_xboole_0(B_526, A_527)), k3_xboole_0(A_527, B_526))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23250, c_18562])).
% 10.24/4.13  tff(c_23576, plain, (![A_528, B_529]: (k5_xboole_0(k3_xboole_0(A_528, B_529), k3_xboole_0(B_529, A_528))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15510, c_17465, c_2, c_15430, c_23289])).
% 10.24/4.13  tff(c_23745, plain, (![A_53, B_54]: (k5_xboole_0(k1_tarski(A_53), k3_xboole_0(k1_tarski(A_53), B_54))=k1_xboole_0 | ~r2_hidden(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_42, c_23576])).
% 10.24/4.13  tff(c_25782, plain, (![A_554, B_555]: (k4_xboole_0(k1_tarski(A_554), B_555)=k1_xboole_0 | ~r2_hidden(A_554, B_555))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_23745])).
% 10.24/4.13  tff(c_14891, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 10.24/4.13  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.24/4.13  tff(c_14995, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14891, c_46])).
% 10.24/4.13  tff(c_25871, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25782, c_14995])).
% 10.24/4.13  tff(c_25929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14890, c_25871])).
% 10.24/4.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.24/4.13  
% 10.24/4.13  Inference rules
% 10.24/4.13  ----------------------
% 10.24/4.13  #Ref     : 0
% 10.24/4.13  #Sup     : 6612
% 10.24/4.13  #Fact    : 0
% 10.24/4.13  #Define  : 0
% 10.24/4.13  #Split   : 2
% 10.24/4.13  #Chain   : 0
% 10.24/4.13  #Close   : 0
% 10.24/4.13  
% 10.24/4.13  Ordering : KBO
% 10.24/4.13  
% 10.24/4.13  Simplification rules
% 10.24/4.13  ----------------------
% 10.24/4.13  #Subsume      : 282
% 10.24/4.13  #Demod        : 7538
% 10.24/4.13  #Tautology    : 3550
% 10.24/4.13  #SimpNegUnit  : 2
% 10.24/4.13  #BackRed      : 10
% 10.24/4.13  
% 10.24/4.13  #Partial instantiations: 0
% 10.24/4.13  #Strategies tried      : 1
% 10.24/4.13  
% 10.24/4.13  Timing (in seconds)
% 10.24/4.13  ----------------------
% 10.24/4.13  Preprocessing        : 0.35
% 10.24/4.13  Parsing              : 0.18
% 10.24/4.13  CNF conversion       : 0.02
% 10.24/4.13  Main loop            : 2.96
% 10.24/4.13  Inferencing          : 0.66
% 10.24/4.14  Reduction            : 1.67
% 10.24/4.14  Demodulation         : 1.50
% 10.24/4.14  BG Simplification    : 0.09
% 10.24/4.14  Subsumption          : 0.39
% 10.24/4.14  Abstraction          : 0.14
% 10.24/4.14  MUC search           : 0.00
% 10.24/4.14  Cooper               : 0.00
% 10.24/4.14  Total                : 3.35
% 10.24/4.14  Index Insertion      : 0.00
% 10.24/4.14  Index Deletion       : 0.00
% 10.24/4.14  Index Matching       : 0.00
% 10.24/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
