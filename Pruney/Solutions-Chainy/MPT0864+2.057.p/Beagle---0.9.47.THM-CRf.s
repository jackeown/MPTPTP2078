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
% DateTime   : Thu Dec  3 10:09:16 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 153 expanded)
%              Number of leaves         :   45 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 176 expanded)
%              Number of equality atoms :   66 ( 138 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_757,plain,(
    ! [E_255,B_256,A_257,D_258,C_254] : k4_enumset1(A_257,A_257,B_256,C_254,D_258,E_255) = k3_enumset1(A_257,B_256,C_254,D_258,E_255) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [A_47,F_52,E_51,D_50,B_48,H_56] : r2_hidden(H_56,k4_enumset1(A_47,B_48,H_56,D_50,E_51,F_52)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_784,plain,(
    ! [B_259,E_263,A_261,C_260,D_262] : r2_hidden(B_259,k3_enumset1(A_261,B_259,C_260,D_262,E_263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_48])).

tff(c_788,plain,(
    ! [A_264,B_265,C_266,D_267] : r2_hidden(A_264,k2_enumset1(A_264,B_265,C_266,D_267)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_784])).

tff(c_792,plain,(
    ! [A_268,B_269,C_270] : r2_hidden(A_268,k1_enumset1(A_268,B_269,C_270)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_788])).

tff(c_805,plain,(
    ! [A_277,B_278] : r2_hidden(A_277,k2_tarski(A_277,B_278)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_792])).

tff(c_808,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_805])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_434,plain,(
    ! [C_152,A_155,D_156,E_153,B_154] : k4_enumset1(A_155,A_155,B_154,C_152,D_156,E_153) = k3_enumset1(A_155,B_154,C_152,D_156,E_153) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_47,F_52,E_51,D_50,C_49,H_56] : r2_hidden(H_56,k4_enumset1(A_47,H_56,C_49,D_50,E_51,F_52)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_461,plain,(
    ! [C_160,B_159,D_161,A_158,E_157] : r2_hidden(A_158,k3_enumset1(A_158,B_159,C_160,D_161,E_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_50])).

tff(c_465,plain,(
    ! [A_162,B_163,C_164,D_165] : r2_hidden(A_162,k2_enumset1(A_162,B_163,C_164,D_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_461])).

tff(c_469,plain,(
    ! [A_166,B_167,C_168] : r2_hidden(A_166,k1_enumset1(A_166,B_167,C_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_465])).

tff(c_473,plain,(
    ! [A_169,B_170] : r2_hidden(A_169,k2_tarski(A_169,B_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_469])).

tff(c_476,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_473])).

tff(c_90,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_104,plain,(
    ! [A_64,B_65] : k1_mcart_1(k4_tarski(A_64,B_65)) = A_64 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_113,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_104])).

tff(c_129,plain,(
    ! [A_67,B_68] : k2_mcart_1(k4_tarski(A_67,B_68)) = B_68 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_138,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_129])).

tff(c_88,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_161,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_138,c_88])).

tff(c_162,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_165,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_90])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_299,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_311,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_299])).

tff(c_318,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_311])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_314,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_299])).

tff(c_328,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_314])).

tff(c_34,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_329,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_34])).

tff(c_374,plain,(
    ! [A_138,B_139] : k2_zfmisc_1(k1_tarski(A_138),k1_tarski(B_139)) = k1_tarski(k4_tarski(A_138,B_139)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( ~ r1_tarski(A_41,k2_zfmisc_1(A_41,B_42))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_380,plain,(
    ! [A_138,B_139] :
      ( ~ r1_tarski(k1_tarski(A_138),k1_tarski(k4_tarski(A_138,B_139)))
      | k1_tarski(A_138) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_32])).

tff(c_391,plain,(
    ! [A_140,B_141] : ~ r1_tarski(k1_tarski(A_140),k1_tarski(k4_tarski(A_140,B_141))) ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_380])).

tff(c_398,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_391])).

tff(c_403,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_398])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_403])).

tff(c_480,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_484,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_90])).

tff(c_589,plain,(
    ! [A_188,B_189] : k5_xboole_0(A_188,k3_xboole_0(A_188,B_189)) = k4_xboole_0(A_188,B_189) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_598,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_589])).

tff(c_604,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_598])).

tff(c_601,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_589])).

tff(c_612,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_601])).

tff(c_613,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_34])).

tff(c_650,plain,(
    ! [A_195,B_196] : k2_zfmisc_1(k1_tarski(A_195),k1_tarski(B_196)) = k1_tarski(k4_tarski(A_195,B_196)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_41,B_42] :
      ( ~ r1_tarski(A_41,k2_zfmisc_1(B_42,A_41))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_659,plain,(
    ! [B_196,A_195] :
      ( ~ r1_tarski(k1_tarski(B_196),k1_tarski(k4_tarski(A_195,B_196)))
      | k1_tarski(B_196) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_30])).

tff(c_706,plain,(
    ! [B_203,A_204] : ~ r1_tarski(k1_tarski(B_203),k1_tarski(k4_tarski(A_204,B_203))) ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_659])).

tff(c_713,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_706])).

tff(c_718,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_713])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:51:46 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.41  
% 2.95/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.95/1.41  
% 2.95/1.41  %Foreground sorts:
% 2.95/1.41  
% 2.95/1.41  
% 2.95/1.41  %Background operators:
% 2.95/1.41  
% 2.95/1.41  
% 2.95/1.41  %Foreground operators:
% 2.95/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.95/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.95/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.95/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.95/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.95/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.95/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.95/1.41  
% 2.95/1.43  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.95/1.43  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.95/1.43  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.95/1.43  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.95/1.43  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.95/1.43  tff(f_90, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 2.95/1.43  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.95/1.43  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.95/1.43  tff(f_96, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.95/1.43  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.95/1.43  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.95/1.43  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.95/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.95/1.43  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.95/1.43  tff(f_66, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.95/1.43  tff(f_59, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.95/1.43  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.43  tff(c_12, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.95/1.43  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.43  tff(c_16, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.95/1.43  tff(c_757, plain, (![E_255, B_256, A_257, D_258, C_254]: (k4_enumset1(A_257, A_257, B_256, C_254, D_258, E_255)=k3_enumset1(A_257, B_256, C_254, D_258, E_255))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.43  tff(c_48, plain, (![A_47, F_52, E_51, D_50, B_48, H_56]: (r2_hidden(H_56, k4_enumset1(A_47, B_48, H_56, D_50, E_51, F_52)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.95/1.43  tff(c_784, plain, (![B_259, E_263, A_261, C_260, D_262]: (r2_hidden(B_259, k3_enumset1(A_261, B_259, C_260, D_262, E_263)))), inference(superposition, [status(thm), theory('equality')], [c_757, c_48])).
% 2.95/1.43  tff(c_788, plain, (![A_264, B_265, C_266, D_267]: (r2_hidden(A_264, k2_enumset1(A_264, B_265, C_266, D_267)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_784])).
% 2.95/1.43  tff(c_792, plain, (![A_268, B_269, C_270]: (r2_hidden(A_268, k1_enumset1(A_268, B_269, C_270)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_788])).
% 2.95/1.43  tff(c_805, plain, (![A_277, B_278]: (r2_hidden(A_277, k2_tarski(A_277, B_278)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_792])).
% 2.95/1.43  tff(c_808, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_805])).
% 2.95/1.43  tff(c_26, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.95/1.43  tff(c_434, plain, (![C_152, A_155, D_156, E_153, B_154]: (k4_enumset1(A_155, A_155, B_154, C_152, D_156, E_153)=k3_enumset1(A_155, B_154, C_152, D_156, E_153))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.43  tff(c_50, plain, (![A_47, F_52, E_51, D_50, C_49, H_56]: (r2_hidden(H_56, k4_enumset1(A_47, H_56, C_49, D_50, E_51, F_52)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.95/1.43  tff(c_461, plain, (![C_160, B_159, D_161, A_158, E_157]: (r2_hidden(A_158, k3_enumset1(A_158, B_159, C_160, D_161, E_157)))), inference(superposition, [status(thm), theory('equality')], [c_434, c_50])).
% 2.95/1.43  tff(c_465, plain, (![A_162, B_163, C_164, D_165]: (r2_hidden(A_162, k2_enumset1(A_162, B_163, C_164, D_165)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_461])).
% 2.95/1.43  tff(c_469, plain, (![A_166, B_167, C_168]: (r2_hidden(A_166, k1_enumset1(A_166, B_167, C_168)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_465])).
% 2.95/1.43  tff(c_473, plain, (![A_169, B_170]: (r2_hidden(A_169, k2_tarski(A_169, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_469])).
% 2.95/1.43  tff(c_476, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_473])).
% 2.95/1.43  tff(c_90, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.95/1.43  tff(c_104, plain, (![A_64, B_65]: (k1_mcart_1(k4_tarski(A_64, B_65))=A_64)), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.95/1.43  tff(c_113, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_90, c_104])).
% 2.95/1.43  tff(c_129, plain, (![A_67, B_68]: (k2_mcart_1(k4_tarski(A_67, B_68))=B_68)), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.95/1.43  tff(c_138, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_90, c_129])).
% 2.95/1.43  tff(c_88, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.95/1.43  tff(c_161, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_138, c_88])).
% 2.95/1.43  tff(c_162, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_161])).
% 2.95/1.43  tff(c_165, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_90])).
% 2.95/1.43  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.43  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.43  tff(c_299, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.95/1.43  tff(c_311, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_299])).
% 2.95/1.43  tff(c_318, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_311])).
% 2.95/1.43  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.95/1.43  tff(c_314, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_299])).
% 2.95/1.43  tff(c_328, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_318, c_314])).
% 2.95/1.43  tff(c_34, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.95/1.43  tff(c_329, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_328, c_34])).
% 2.95/1.43  tff(c_374, plain, (![A_138, B_139]: (k2_zfmisc_1(k1_tarski(A_138), k1_tarski(B_139))=k1_tarski(k4_tarski(A_138, B_139)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.95/1.43  tff(c_32, plain, (![A_41, B_42]: (~r1_tarski(A_41, k2_zfmisc_1(A_41, B_42)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.95/1.43  tff(c_380, plain, (![A_138, B_139]: (~r1_tarski(k1_tarski(A_138), k1_tarski(k4_tarski(A_138, B_139))) | k1_tarski(A_138)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_374, c_32])).
% 2.95/1.43  tff(c_391, plain, (![A_140, B_141]: (~r1_tarski(k1_tarski(A_140), k1_tarski(k4_tarski(A_140, B_141))))), inference(negUnitSimplification, [status(thm)], [c_329, c_380])).
% 2.95/1.43  tff(c_398, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_391])).
% 2.95/1.43  tff(c_403, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_398])).
% 2.95/1.43  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_476, c_403])).
% 2.95/1.43  tff(c_480, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_161])).
% 2.95/1.43  tff(c_484, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_90])).
% 2.95/1.43  tff(c_589, plain, (![A_188, B_189]: (k5_xboole_0(A_188, k3_xboole_0(A_188, B_189))=k4_xboole_0(A_188, B_189))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.95/1.43  tff(c_598, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_589])).
% 2.95/1.43  tff(c_604, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_598])).
% 2.95/1.43  tff(c_601, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_589])).
% 2.95/1.43  tff(c_612, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_604, c_601])).
% 2.95/1.43  tff(c_613, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_612, c_34])).
% 2.95/1.43  tff(c_650, plain, (![A_195, B_196]: (k2_zfmisc_1(k1_tarski(A_195), k1_tarski(B_196))=k1_tarski(k4_tarski(A_195, B_196)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.95/1.43  tff(c_30, plain, (![A_41, B_42]: (~r1_tarski(A_41, k2_zfmisc_1(B_42, A_41)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.95/1.43  tff(c_659, plain, (![B_196, A_195]: (~r1_tarski(k1_tarski(B_196), k1_tarski(k4_tarski(A_195, B_196))) | k1_tarski(B_196)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_650, c_30])).
% 2.95/1.43  tff(c_706, plain, (![B_203, A_204]: (~r1_tarski(k1_tarski(B_203), k1_tarski(k4_tarski(A_204, B_203))))), inference(negUnitSimplification, [status(thm)], [c_613, c_659])).
% 2.95/1.43  tff(c_713, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_484, c_706])).
% 2.95/1.43  tff(c_718, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_713])).
% 2.95/1.43  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_808, c_718])).
% 2.95/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.43  
% 2.95/1.43  Inference rules
% 2.95/1.43  ----------------------
% 2.95/1.43  #Ref     : 0
% 2.95/1.43  #Sup     : 174
% 2.95/1.43  #Fact    : 0
% 2.95/1.43  #Define  : 0
% 2.95/1.43  #Split   : 1
% 2.95/1.43  #Chain   : 0
% 2.95/1.43  #Close   : 0
% 2.95/1.43  
% 2.95/1.43  Ordering : KBO
% 2.95/1.43  
% 2.95/1.43  Simplification rules
% 2.95/1.43  ----------------------
% 2.95/1.43  #Subsume      : 6
% 2.95/1.43  #Demod        : 29
% 2.95/1.43  #Tautology    : 114
% 2.95/1.43  #SimpNegUnit  : 10
% 2.95/1.43  #BackRed      : 9
% 2.95/1.43  
% 2.95/1.43  #Partial instantiations: 0
% 2.95/1.43  #Strategies tried      : 1
% 2.95/1.43  
% 2.95/1.43  Timing (in seconds)
% 2.95/1.43  ----------------------
% 2.95/1.43  Preprocessing        : 0.35
% 2.95/1.43  Parsing              : 0.17
% 2.95/1.43  CNF conversion       : 0.03
% 2.95/1.43  Main loop            : 0.33
% 2.95/1.43  Inferencing          : 0.11
% 2.95/1.43  Reduction            : 0.10
% 2.95/1.43  Demodulation         : 0.07
% 2.95/1.43  BG Simplification    : 0.02
% 2.95/1.43  Subsumption          : 0.07
% 2.95/1.43  Abstraction          : 0.02
% 2.95/1.43  MUC search           : 0.00
% 2.95/1.43  Cooper               : 0.00
% 2.95/1.43  Total                : 0.72
% 2.95/1.43  Index Insertion      : 0.00
% 2.95/1.43  Index Deletion       : 0.00
% 2.95/1.43  Index Matching       : 0.00
% 2.95/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
