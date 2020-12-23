%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:02 EST 2020

% Result     : Theorem 9.90s
% Output     : CNFRefutation 10.02s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 356 expanded)
%              Number of leaves         :   35 ( 134 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 368 expanded)
%              Number of equality atoms :  104 ( 324 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_48,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_234,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_336,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_353,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_336])).

tff(c_356,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_353])).

tff(c_36,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_357,plain,(
    ! [B_49] : k1_tarski(B_49) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_36])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [B_60,A_61] : k5_xboole_0(B_60,A_61) = k5_xboole_0(A_61,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [A_61] : k5_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_8])).

tff(c_734,plain,(
    ! [A_99,B_100,C_101] : k5_xboole_0(k5_xboole_0(A_99,B_100),C_101) = k5_xboole_0(A_99,k5_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_844,plain,(
    ! [A_11,C_101] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_101)) = k5_xboole_0(k1_xboole_0,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_734])).

tff(c_860,plain,(
    ! [A_102,C_103] : k5_xboole_0(A_102,k5_xboole_0(A_102,C_103)) = C_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_844])).

tff(c_918,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_860])).

tff(c_940,plain,(
    ! [A_104,B_105] : k5_xboole_0(A_104,k5_xboole_0(B_105,A_104)) = B_105 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_860])).

tff(c_970,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),B_2) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_940])).

tff(c_16,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_237,plain,(
    ! [A_63,B_64] : k3_tarski(k2_tarski(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_275,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(B_70,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_237])).

tff(c_34,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_281,plain,(
    ! [B_70,A_69] : k2_xboole_0(B_70,A_69) = k2_xboole_0(A_69,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_34])).

tff(c_52,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_414,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k2_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5591,plain,(
    ! [A_180,B_181] : k5_xboole_0(A_180,k5_xboole_0(B_181,k2_xboole_0(A_180,B_181))) = k3_xboole_0(A_180,B_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_14])).

tff(c_859,plain,(
    ! [A_11,C_101] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_101)) = C_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_844])).

tff(c_5638,plain,(
    ! [B_181,A_180] : k5_xboole_0(B_181,k2_xboole_0(A_180,B_181)) = k5_xboole_0(A_180,k3_xboole_0(A_180,B_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5591,c_859])).

tff(c_5796,plain,(
    ! [B_183,A_184] : k5_xboole_0(B_183,k2_xboole_0(A_184,B_183)) = k4_xboole_0(A_184,B_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5638])).

tff(c_6125,plain,(
    ! [A_187,B_188] : k5_xboole_0(k2_xboole_0(A_187,B_188),k4_xboole_0(A_187,B_188)) = B_188 ),
    inference(superposition,[status(thm),theory(equality)],[c_5796,c_918])).

tff(c_6185,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_6125])).

tff(c_6214,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_281,c_6185])).

tff(c_6228,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k1_tarski('#skF_3')),'#skF_4') = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6214,c_14])).

tff(c_6231,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_6228])).

tff(c_44,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,k1_tarski(B_52)) = A_51
      | r2_hidden(B_52,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1436,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k4_xboole_0(A_135,B_136)) = k3_xboole_0(A_135,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_860])).

tff(c_1487,plain,(
    ! [A_51,B_52] :
      ( k5_xboole_0(A_51,A_51) = k3_xboole_0(A_51,k1_tarski(B_52))
      | r2_hidden(B_52,A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1436])).

tff(c_1503,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,k1_tarski(B_52)) = k1_xboole_0
      | r2_hidden(B_52,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1487])).

tff(c_6242,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6231,c_1503])).

tff(c_6261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_357,c_6242])).

tff(c_6262,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k5_xboole_0(k5_xboole_0(A_8,B_9),C_10) = k5_xboole_0(A_8,k5_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6531,plain,(
    ! [A_207,B_208] : k5_xboole_0(k5_xboole_0(A_207,B_208),k2_xboole_0(A_207,B_208)) = k3_xboole_0(A_207,B_208) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10744,plain,(
    ! [A_284,B_285] : k5_xboole_0(A_284,k5_xboole_0(B_285,k2_xboole_0(A_284,B_285))) = k3_xboole_0(A_284,B_285) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6531])).

tff(c_6388,plain,(
    ! [A_202,B_203,C_204] : k5_xboole_0(k5_xboole_0(A_202,B_203),C_204) = k5_xboole_0(A_202,k5_xboole_0(B_203,C_204)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6452,plain,(
    ! [A_11,C_204] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_204)) = k5_xboole_0(k1_xboole_0,C_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6388])).

tff(c_6465,plain,(
    ! [A_11,C_204] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_204)) = C_204 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_6452])).

tff(c_10790,plain,(
    ! [B_285,A_284] : k5_xboole_0(B_285,k2_xboole_0(A_284,B_285)) = k5_xboole_0(A_284,k3_xboole_0(A_284,B_285)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10744,c_6465])).

tff(c_10885,plain,(
    ! [B_286,A_287] : k5_xboole_0(B_286,k2_xboole_0(A_287,B_286)) = k4_xboole_0(A_287,B_286) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10790])).

tff(c_10940,plain,(
    ! [B_286,A_287] : k5_xboole_0(B_286,k4_xboole_0(A_287,B_286)) = k2_xboole_0(A_287,B_286) ),
    inference(superposition,[status(thm),theory(equality)],[c_10885,c_6465])).

tff(c_6340,plain,(
    ! [B_197,A_198] :
      ( k3_xboole_0(B_197,k1_tarski(A_198)) = k1_tarski(A_198)
      | ~ r2_hidden(A_198,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15721,plain,(
    ! [B_339,A_340] :
      ( k5_xboole_0(B_339,k1_tarski(A_340)) = k4_xboole_0(B_339,k1_tarski(A_340))
      | ~ r2_hidden(A_340,B_339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6340,c_6])).

tff(c_6466,plain,(
    ! [A_205,C_206] : k5_xboole_0(A_205,k5_xboole_0(A_205,C_206)) = C_206 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_6452])).

tff(c_6509,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6466])).

tff(c_15832,plain,(
    ! [A_340,B_339] :
      ( k5_xboole_0(k1_tarski(A_340),k4_xboole_0(B_339,k1_tarski(A_340))) = B_339
      | ~ r2_hidden(A_340,B_339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15721,c_6509])).

tff(c_15986,plain,(
    ! [B_341,A_342] :
      ( k2_xboole_0(B_341,k1_tarski(A_342)) = B_341
      | ~ r2_hidden(A_342,B_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10940,c_15832])).

tff(c_10978,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k2_xboole_0(A_69,B_70)) = k4_xboole_0(B_70,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_10885])).

tff(c_16007,plain,(
    ! [B_341,A_342] :
      ( k5_xboole_0(B_341,B_341) = k4_xboole_0(k1_tarski(A_342),B_341)
      | ~ r2_hidden(A_342,B_341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15986,c_10978])).

tff(c_16554,plain,(
    ! [A_348,B_349] :
      ( k4_xboole_0(k1_tarski(A_348),B_349) = k1_xboole_0
      | ~ r2_hidden(A_348,B_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16007])).

tff(c_6263,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6280,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6263,c_50])).

tff(c_16614,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16554,c_6280])).

tff(c_16672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6262,c_16614])).

tff(c_16673,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_17073,plain,(
    ! [A_384,B_385,C_386] : k5_xboole_0(k5_xboole_0(A_384,B_385),C_386) = k5_xboole_0(A_384,k5_xboole_0(B_385,C_386)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_17161,plain,(
    ! [A_11,C_386] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_386)) = k5_xboole_0(k1_xboole_0,C_386) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_17073])).

tff(c_17177,plain,(
    ! [A_387,C_388] : k5_xboole_0(A_387,k5_xboole_0(A_387,C_388)) = C_388 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_17161])).

tff(c_17219,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_17177])).

tff(c_16676,plain,(
    ! [A_350,B_351] : k3_tarski(k2_tarski(A_350,B_351)) = k2_xboole_0(A_350,B_351) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16717,plain,(
    ! [A_356,B_357] : k3_tarski(k2_tarski(A_356,B_357)) = k2_xboole_0(B_357,A_356) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16676])).

tff(c_16723,plain,(
    ! [B_357,A_356] : k2_xboole_0(B_357,A_356) = k2_xboole_0(A_356,B_357) ),
    inference(superposition,[status(thm),theory(equality)],[c_16717,c_34])).

tff(c_18404,plain,(
    ! [A_435,B_436] : k5_xboole_0(A_435,k5_xboole_0(B_436,k2_xboole_0(A_435,B_436))) = k3_xboole_0(A_435,B_436) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_17073])).

tff(c_17176,plain,(
    ! [A_11,C_386] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_386)) = C_386 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_17161])).

tff(c_18419,plain,(
    ! [B_436,A_435] : k5_xboole_0(B_436,k2_xboole_0(A_435,B_436)) = k5_xboole_0(A_435,k3_xboole_0(A_435,B_436)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18404,c_17176])).

tff(c_18496,plain,(
    ! [B_437,A_438] : k5_xboole_0(B_437,k2_xboole_0(A_438,B_437)) = k4_xboole_0(A_438,B_437) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18419])).

tff(c_18558,plain,(
    ! [B_357,A_356] : k5_xboole_0(B_357,k2_xboole_0(B_357,A_356)) = k4_xboole_0(A_356,B_357) ),
    inference(superposition,[status(thm),theory(equality)],[c_16723,c_18496])).

tff(c_16980,plain,(
    ! [A_381,B_382] : k5_xboole_0(k5_xboole_0(A_381,B_382),k2_xboole_0(A_381,B_382)) = k3_xboole_0(A_381,B_382) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19440,plain,(
    ! [A_451,B_452] : k5_xboole_0(k5_xboole_0(A_451,B_452),k2_xboole_0(B_452,A_451)) = k3_xboole_0(B_452,A_451) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16980])).

tff(c_19467,plain,(
    ! [A_451,B_452] : k5_xboole_0(A_451,k5_xboole_0(B_452,k2_xboole_0(B_452,A_451))) = k3_xboole_0(B_452,A_451) ),
    inference(superposition,[status(thm),theory(equality)],[c_19440,c_10])).

tff(c_19633,plain,(
    ! [B_453,A_454] : k3_xboole_0(B_453,A_454) = k3_xboole_0(A_454,B_453) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17219,c_18558,c_19467])).

tff(c_19722,plain,(
    ! [A_454,B_453] : k5_xboole_0(A_454,k3_xboole_0(B_453,A_454)) = k4_xboole_0(A_454,B_453) ),
    inference(superposition,[status(thm),theory(equality)],[c_19633,c_6])).

tff(c_17100,plain,(
    ! [C_386,A_384,B_385] : k5_xboole_0(C_386,k5_xboole_0(A_384,B_385)) = k5_xboole_0(A_384,k5_xboole_0(B_385,C_386)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17073,c_2])).

tff(c_16941,plain,(
    ! [B_379,A_380] :
      ( k3_xboole_0(B_379,k1_tarski(A_380)) = k1_tarski(A_380)
      | ~ r2_hidden(A_380,B_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25850,plain,(
    ! [B_515,A_516] :
      ( k5_xboole_0(B_515,k1_tarski(A_516)) = k4_xboole_0(B_515,k1_tarski(A_516))
      | ~ r2_hidden(A_516,B_515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16941,c_6])).

tff(c_22248,plain,(
    ! [C_487,A_488,B_489] : k5_xboole_0(C_487,k5_xboole_0(A_488,B_489)) = k5_xboole_0(A_488,k5_xboole_0(B_489,C_487)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17073,c_2])).

tff(c_23111,plain,(
    ! [A_490,C_491] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_490,C_491)) = k5_xboole_0(C_491,A_490) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_22248])).

tff(c_17229,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17177])).

tff(c_23147,plain,(
    ! [A_490,C_491] : k5_xboole_0(k5_xboole_0(A_490,C_491),k5_xboole_0(C_491,A_490)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_23111,c_17229])).

tff(c_25867,plain,(
    ! [B_515,A_516] :
      ( k5_xboole_0(k4_xboole_0(B_515,k1_tarski(A_516)),k5_xboole_0(k1_tarski(A_516),B_515)) = k1_xboole_0
      | ~ r2_hidden(A_516,B_515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25850,c_23147])).

tff(c_26356,plain,(
    ! [A_521,B_522] :
      ( k4_xboole_0(k1_tarski(A_521),B_522) = k1_xboole_0
      | ~ r2_hidden(A_521,B_522) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19722,c_17219,c_17100,c_25867])).

tff(c_16674,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16707,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16674,c_46])).

tff(c_26428,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26356,c_16707])).

tff(c_26475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16673,c_26428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.90/4.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.95/4.13  
% 9.95/4.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.95/4.13  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.95/4.13  
% 9.95/4.13  %Foreground sorts:
% 9.95/4.13  
% 9.95/4.13  
% 9.95/4.13  %Background operators:
% 9.95/4.13  
% 9.95/4.13  
% 9.95/4.13  %Foreground operators:
% 9.95/4.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.95/4.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.95/4.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.95/4.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.95/4.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.95/4.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.95/4.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.95/4.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.95/4.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.95/4.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.95/4.13  tff('#skF_2', type, '#skF_2': $i).
% 9.95/4.13  tff('#skF_3', type, '#skF_3': $i).
% 9.95/4.13  tff('#skF_1', type, '#skF_1': $i).
% 9.95/4.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.95/4.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.95/4.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.95/4.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.95/4.13  tff('#skF_4', type, '#skF_4': $i).
% 9.95/4.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.95/4.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.95/4.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.95/4.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.95/4.13  
% 10.02/4.15  tff(f_78, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 10.02/4.15  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.02/4.15  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.02/4.15  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.02/4.15  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 10.02/4.15  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.02/4.15  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.02/4.15  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.02/4.15  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.02/4.15  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.02/4.15  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.02/4.15  tff(f_73, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.02/4.15  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 10.02/4.15  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.02/4.15  tff(c_234, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 10.02/4.15  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.02/4.15  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.02/4.15  tff(c_336, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.02/4.15  tff(c_353, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_336])).
% 10.02/4.15  tff(c_356, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_353])).
% 10.02/4.15  tff(c_36, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.02/4.15  tff(c_357, plain, (![B_49]: (k1_tarski(B_49)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_356, c_36])).
% 10.02/4.15  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.02/4.15  tff(c_139, plain, (![B_60, A_61]: (k5_xboole_0(B_60, A_61)=k5_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.02/4.15  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.02/4.15  tff(c_155, plain, (![A_61]: (k5_xboole_0(k1_xboole_0, A_61)=A_61)), inference(superposition, [status(thm), theory('equality')], [c_139, c_8])).
% 10.02/4.15  tff(c_734, plain, (![A_99, B_100, C_101]: (k5_xboole_0(k5_xboole_0(A_99, B_100), C_101)=k5_xboole_0(A_99, k5_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.02/4.15  tff(c_844, plain, (![A_11, C_101]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_101))=k5_xboole_0(k1_xboole_0, C_101))), inference(superposition, [status(thm), theory('equality')], [c_12, c_734])).
% 10.02/4.15  tff(c_860, plain, (![A_102, C_103]: (k5_xboole_0(A_102, k5_xboole_0(A_102, C_103))=C_103)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_844])).
% 10.02/4.15  tff(c_918, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_860])).
% 10.02/4.15  tff(c_940, plain, (![A_104, B_105]: (k5_xboole_0(A_104, k5_xboole_0(B_105, A_104))=B_105)), inference(superposition, [status(thm), theory('equality')], [c_2, c_860])).
% 10.02/4.15  tff(c_970, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), B_2)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_918, c_940])).
% 10.02/4.15  tff(c_16, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.02/4.15  tff(c_237, plain, (![A_63, B_64]: (k3_tarski(k2_tarski(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.02/4.15  tff(c_275, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(B_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_16, c_237])).
% 10.02/4.15  tff(c_34, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.02/4.15  tff(c_281, plain, (![B_70, A_69]: (k2_xboole_0(B_70, A_69)=k2_xboole_0(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_275, c_34])).
% 10.02/4.15  tff(c_52, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.02/4.15  tff(c_414, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 10.02/4.15  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.02/4.15  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k2_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.02/4.15  tff(c_5591, plain, (![A_180, B_181]: (k5_xboole_0(A_180, k5_xboole_0(B_181, k2_xboole_0(A_180, B_181)))=k3_xboole_0(A_180, B_181))), inference(superposition, [status(thm), theory('equality')], [c_734, c_14])).
% 10.02/4.15  tff(c_859, plain, (![A_11, C_101]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_101))=C_101)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_844])).
% 10.02/4.15  tff(c_5638, plain, (![B_181, A_180]: (k5_xboole_0(B_181, k2_xboole_0(A_180, B_181))=k5_xboole_0(A_180, k3_xboole_0(A_180, B_181)))), inference(superposition, [status(thm), theory('equality')], [c_5591, c_859])).
% 10.02/4.15  tff(c_5796, plain, (![B_183, A_184]: (k5_xboole_0(B_183, k2_xboole_0(A_184, B_183))=k4_xboole_0(A_184, B_183))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5638])).
% 10.02/4.15  tff(c_6125, plain, (![A_187, B_188]: (k5_xboole_0(k2_xboole_0(A_187, B_188), k4_xboole_0(A_187, B_188))=B_188)), inference(superposition, [status(thm), theory('equality')], [c_5796, c_918])).
% 10.02/4.15  tff(c_6185, plain, (k5_xboole_0(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_414, c_6125])).
% 10.02/4.15  tff(c_6214, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_281, c_6185])).
% 10.02/4.15  tff(c_6228, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k1_tarski('#skF_3')), '#skF_4')=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6214, c_14])).
% 10.02/4.15  tff(c_6231, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_970, c_6228])).
% 10.02/4.15  tff(c_44, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k1_tarski(B_52))=A_51 | r2_hidden(B_52, A_51))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.02/4.15  tff(c_1436, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k4_xboole_0(A_135, B_136))=k3_xboole_0(A_135, B_136))), inference(superposition, [status(thm), theory('equality')], [c_6, c_860])).
% 10.02/4.15  tff(c_1487, plain, (![A_51, B_52]: (k5_xboole_0(A_51, A_51)=k3_xboole_0(A_51, k1_tarski(B_52)) | r2_hidden(B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1436])).
% 10.02/4.15  tff(c_1503, plain, (![A_51, B_52]: (k3_xboole_0(A_51, k1_tarski(B_52))=k1_xboole_0 | r2_hidden(B_52, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1487])).
% 10.02/4.15  tff(c_6242, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6231, c_1503])).
% 10.02/4.15  tff(c_6261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_357, c_6242])).
% 10.02/4.15  tff(c_6262, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 10.02/4.15  tff(c_10, plain, (![A_8, B_9, C_10]: (k5_xboole_0(k5_xboole_0(A_8, B_9), C_10)=k5_xboole_0(A_8, k5_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.02/4.15  tff(c_6531, plain, (![A_207, B_208]: (k5_xboole_0(k5_xboole_0(A_207, B_208), k2_xboole_0(A_207, B_208))=k3_xboole_0(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.02/4.15  tff(c_10744, plain, (![A_284, B_285]: (k5_xboole_0(A_284, k5_xboole_0(B_285, k2_xboole_0(A_284, B_285)))=k3_xboole_0(A_284, B_285))), inference(superposition, [status(thm), theory('equality')], [c_10, c_6531])).
% 10.02/4.15  tff(c_6388, plain, (![A_202, B_203, C_204]: (k5_xboole_0(k5_xboole_0(A_202, B_203), C_204)=k5_xboole_0(A_202, k5_xboole_0(B_203, C_204)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.02/4.15  tff(c_6452, plain, (![A_11, C_204]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_204))=k5_xboole_0(k1_xboole_0, C_204))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6388])).
% 10.02/4.15  tff(c_6465, plain, (![A_11, C_204]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_204))=C_204)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_6452])).
% 10.02/4.15  tff(c_10790, plain, (![B_285, A_284]: (k5_xboole_0(B_285, k2_xboole_0(A_284, B_285))=k5_xboole_0(A_284, k3_xboole_0(A_284, B_285)))), inference(superposition, [status(thm), theory('equality')], [c_10744, c_6465])).
% 10.02/4.15  tff(c_10885, plain, (![B_286, A_287]: (k5_xboole_0(B_286, k2_xboole_0(A_287, B_286))=k4_xboole_0(A_287, B_286))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10790])).
% 10.02/4.15  tff(c_10940, plain, (![B_286, A_287]: (k5_xboole_0(B_286, k4_xboole_0(A_287, B_286))=k2_xboole_0(A_287, B_286))), inference(superposition, [status(thm), theory('equality')], [c_10885, c_6465])).
% 10.02/4.15  tff(c_6340, plain, (![B_197, A_198]: (k3_xboole_0(B_197, k1_tarski(A_198))=k1_tarski(A_198) | ~r2_hidden(A_198, B_197))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.02/4.15  tff(c_15721, plain, (![B_339, A_340]: (k5_xboole_0(B_339, k1_tarski(A_340))=k4_xboole_0(B_339, k1_tarski(A_340)) | ~r2_hidden(A_340, B_339))), inference(superposition, [status(thm), theory('equality')], [c_6340, c_6])).
% 10.02/4.15  tff(c_6466, plain, (![A_205, C_206]: (k5_xboole_0(A_205, k5_xboole_0(A_205, C_206))=C_206)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_6452])).
% 10.02/4.15  tff(c_6509, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6466])).
% 10.02/4.15  tff(c_15832, plain, (![A_340, B_339]: (k5_xboole_0(k1_tarski(A_340), k4_xboole_0(B_339, k1_tarski(A_340)))=B_339 | ~r2_hidden(A_340, B_339))), inference(superposition, [status(thm), theory('equality')], [c_15721, c_6509])).
% 10.02/4.15  tff(c_15986, plain, (![B_341, A_342]: (k2_xboole_0(B_341, k1_tarski(A_342))=B_341 | ~r2_hidden(A_342, B_341))), inference(demodulation, [status(thm), theory('equality')], [c_10940, c_15832])).
% 10.02/4.15  tff(c_10978, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k2_xboole_0(A_69, B_70))=k4_xboole_0(B_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_281, c_10885])).
% 10.02/4.15  tff(c_16007, plain, (![B_341, A_342]: (k5_xboole_0(B_341, B_341)=k4_xboole_0(k1_tarski(A_342), B_341) | ~r2_hidden(A_342, B_341))), inference(superposition, [status(thm), theory('equality')], [c_15986, c_10978])).
% 10.02/4.15  tff(c_16554, plain, (![A_348, B_349]: (k4_xboole_0(k1_tarski(A_348), B_349)=k1_xboole_0 | ~r2_hidden(A_348, B_349))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16007])).
% 10.02/4.15  tff(c_6263, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 10.02/4.15  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.02/4.15  tff(c_6280, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6263, c_50])).
% 10.02/4.15  tff(c_16614, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16554, c_6280])).
% 10.02/4.15  tff(c_16672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6262, c_16614])).
% 10.02/4.15  tff(c_16673, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 10.02/4.15  tff(c_17073, plain, (![A_384, B_385, C_386]: (k5_xboole_0(k5_xboole_0(A_384, B_385), C_386)=k5_xboole_0(A_384, k5_xboole_0(B_385, C_386)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.02/4.15  tff(c_17161, plain, (![A_11, C_386]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_386))=k5_xboole_0(k1_xboole_0, C_386))), inference(superposition, [status(thm), theory('equality')], [c_12, c_17073])).
% 10.02/4.15  tff(c_17177, plain, (![A_387, C_388]: (k5_xboole_0(A_387, k5_xboole_0(A_387, C_388))=C_388)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_17161])).
% 10.02/4.15  tff(c_17219, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_17177])).
% 10.02/4.15  tff(c_16676, plain, (![A_350, B_351]: (k3_tarski(k2_tarski(A_350, B_351))=k2_xboole_0(A_350, B_351))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.02/4.15  tff(c_16717, plain, (![A_356, B_357]: (k3_tarski(k2_tarski(A_356, B_357))=k2_xboole_0(B_357, A_356))), inference(superposition, [status(thm), theory('equality')], [c_16, c_16676])).
% 10.02/4.15  tff(c_16723, plain, (![B_357, A_356]: (k2_xboole_0(B_357, A_356)=k2_xboole_0(A_356, B_357))), inference(superposition, [status(thm), theory('equality')], [c_16717, c_34])).
% 10.02/4.15  tff(c_18404, plain, (![A_435, B_436]: (k5_xboole_0(A_435, k5_xboole_0(B_436, k2_xboole_0(A_435, B_436)))=k3_xboole_0(A_435, B_436))), inference(superposition, [status(thm), theory('equality')], [c_14, c_17073])).
% 10.02/4.15  tff(c_17176, plain, (![A_11, C_386]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_386))=C_386)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_17161])).
% 10.02/4.15  tff(c_18419, plain, (![B_436, A_435]: (k5_xboole_0(B_436, k2_xboole_0(A_435, B_436))=k5_xboole_0(A_435, k3_xboole_0(A_435, B_436)))), inference(superposition, [status(thm), theory('equality')], [c_18404, c_17176])).
% 10.02/4.15  tff(c_18496, plain, (![B_437, A_438]: (k5_xboole_0(B_437, k2_xboole_0(A_438, B_437))=k4_xboole_0(A_438, B_437))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18419])).
% 10.02/4.15  tff(c_18558, plain, (![B_357, A_356]: (k5_xboole_0(B_357, k2_xboole_0(B_357, A_356))=k4_xboole_0(A_356, B_357))), inference(superposition, [status(thm), theory('equality')], [c_16723, c_18496])).
% 10.02/4.15  tff(c_16980, plain, (![A_381, B_382]: (k5_xboole_0(k5_xboole_0(A_381, B_382), k2_xboole_0(A_381, B_382))=k3_xboole_0(A_381, B_382))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.02/4.15  tff(c_19440, plain, (![A_451, B_452]: (k5_xboole_0(k5_xboole_0(A_451, B_452), k2_xboole_0(B_452, A_451))=k3_xboole_0(B_452, A_451))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16980])).
% 10.02/4.15  tff(c_19467, plain, (![A_451, B_452]: (k5_xboole_0(A_451, k5_xboole_0(B_452, k2_xboole_0(B_452, A_451)))=k3_xboole_0(B_452, A_451))), inference(superposition, [status(thm), theory('equality')], [c_19440, c_10])).
% 10.02/4.15  tff(c_19633, plain, (![B_453, A_454]: (k3_xboole_0(B_453, A_454)=k3_xboole_0(A_454, B_453))), inference(demodulation, [status(thm), theory('equality')], [c_17219, c_18558, c_19467])).
% 10.02/4.15  tff(c_19722, plain, (![A_454, B_453]: (k5_xboole_0(A_454, k3_xboole_0(B_453, A_454))=k4_xboole_0(A_454, B_453))), inference(superposition, [status(thm), theory('equality')], [c_19633, c_6])).
% 10.02/4.15  tff(c_17100, plain, (![C_386, A_384, B_385]: (k5_xboole_0(C_386, k5_xboole_0(A_384, B_385))=k5_xboole_0(A_384, k5_xboole_0(B_385, C_386)))), inference(superposition, [status(thm), theory('equality')], [c_17073, c_2])).
% 10.02/4.15  tff(c_16941, plain, (![B_379, A_380]: (k3_xboole_0(B_379, k1_tarski(A_380))=k1_tarski(A_380) | ~r2_hidden(A_380, B_379))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.02/4.15  tff(c_25850, plain, (![B_515, A_516]: (k5_xboole_0(B_515, k1_tarski(A_516))=k4_xboole_0(B_515, k1_tarski(A_516)) | ~r2_hidden(A_516, B_515))), inference(superposition, [status(thm), theory('equality')], [c_16941, c_6])).
% 10.02/4.15  tff(c_22248, plain, (![C_487, A_488, B_489]: (k5_xboole_0(C_487, k5_xboole_0(A_488, B_489))=k5_xboole_0(A_488, k5_xboole_0(B_489, C_487)))), inference(superposition, [status(thm), theory('equality')], [c_17073, c_2])).
% 10.02/4.15  tff(c_23111, plain, (![A_490, C_491]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_490, C_491))=k5_xboole_0(C_491, A_490))), inference(superposition, [status(thm), theory('equality')], [c_155, c_22248])).
% 10.02/4.15  tff(c_17229, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_17177])).
% 10.02/4.15  tff(c_23147, plain, (![A_490, C_491]: (k5_xboole_0(k5_xboole_0(A_490, C_491), k5_xboole_0(C_491, A_490))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23111, c_17229])).
% 10.02/4.15  tff(c_25867, plain, (![B_515, A_516]: (k5_xboole_0(k4_xboole_0(B_515, k1_tarski(A_516)), k5_xboole_0(k1_tarski(A_516), B_515))=k1_xboole_0 | ~r2_hidden(A_516, B_515))), inference(superposition, [status(thm), theory('equality')], [c_25850, c_23147])).
% 10.02/4.15  tff(c_26356, plain, (![A_521, B_522]: (k4_xboole_0(k1_tarski(A_521), B_522)=k1_xboole_0 | ~r2_hidden(A_521, B_522))), inference(demodulation, [status(thm), theory('equality')], [c_19722, c_17219, c_17100, c_25867])).
% 10.02/4.15  tff(c_16674, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 10.02/4.15  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.02/4.15  tff(c_16707, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16674, c_46])).
% 10.02/4.15  tff(c_26428, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26356, c_16707])).
% 10.02/4.15  tff(c_26475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16673, c_26428])).
% 10.02/4.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.02/4.15  
% 10.02/4.15  Inference rules
% 10.02/4.15  ----------------------
% 10.02/4.15  #Ref     : 0
% 10.02/4.15  #Sup     : 6527
% 10.02/4.15  #Fact    : 0
% 10.02/4.15  #Define  : 0
% 10.02/4.15  #Split   : 2
% 10.02/4.15  #Chain   : 0
% 10.02/4.15  #Close   : 0
% 10.02/4.15  
% 10.02/4.15  Ordering : KBO
% 10.02/4.15  
% 10.02/4.15  Simplification rules
% 10.02/4.15  ----------------------
% 10.02/4.15  #Subsume      : 575
% 10.02/4.15  #Demod        : 6222
% 10.02/4.15  #Tautology    : 3318
% 10.02/4.15  #SimpNegUnit  : 59
% 10.02/4.15  #BackRed      : 5
% 10.02/4.15  
% 10.02/4.15  #Partial instantiations: 0
% 10.02/4.15  #Strategies tried      : 1
% 10.02/4.15  
% 10.02/4.15  Timing (in seconds)
% 10.02/4.15  ----------------------
% 10.02/4.15  Preprocessing        : 0.32
% 10.02/4.15  Parsing              : 0.17
% 10.02/4.15  CNF conversion       : 0.02
% 10.02/4.15  Main loop            : 3.07
% 10.02/4.15  Inferencing          : 0.68
% 10.02/4.15  Reduction            : 1.72
% 10.02/4.15  Demodulation         : 1.53
% 10.02/4.15  BG Simplification    : 0.10
% 10.02/4.15  Subsumption          : 0.41
% 10.02/4.15  Abstraction          : 0.15
% 10.02/4.15  MUC search           : 0.00
% 10.02/4.15  Cooper               : 0.00
% 10.02/4.15  Total                : 3.43
% 10.02/4.15  Index Insertion      : 0.00
% 10.02/4.15  Index Deletion       : 0.00
% 10.02/4.15  Index Matching       : 0.00
% 10.02/4.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
