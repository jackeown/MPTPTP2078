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
% DateTime   : Thu Dec  3 10:09:17 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 139 expanded)
%              Number of leaves         :   42 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 168 expanded)
%              Number of equality atoms :   62 ( 130 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k4_enumset1(A_16,A_16,B_17,C_18,D_19,E_20) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_954,plain,(
    ! [C_315,B_317,E_318,F_316,D_314,A_313] : k5_enumset1(A_313,A_313,B_317,C_315,D_314,E_318,F_316) = k4_enumset1(A_313,B_317,C_315,D_314,E_318,F_316) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [G_49,I_53,E_47,F_48,D_46,C_45,A_43] : r2_hidden(I_53,k5_enumset1(A_43,I_53,C_45,D_46,E_47,F_48,G_49)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_992,plain,(
    ! [A_326,B_323,D_322,F_321,E_325,C_324] : r2_hidden(A_326,k4_enumset1(A_326,B_323,C_324,D_322,E_325,F_321)) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_50])).

tff(c_1005,plain,(
    ! [C_338,B_334,A_336,E_335,D_337] : r2_hidden(A_336,k3_enumset1(A_336,B_334,C_338,D_337,E_335)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_992])).

tff(c_1009,plain,(
    ! [A_339,B_340,C_341,D_342] : r2_hidden(A_339,k2_enumset1(A_339,B_340,C_341,D_342)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1005])).

tff(c_1013,plain,(
    ! [A_343,B_344,C_345] : r2_hidden(A_343,k1_enumset1(A_343,B_344,C_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1009])).

tff(c_1016,plain,(
    ! [A_7,B_8] : r2_hidden(A_7,k2_tarski(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1013])).

tff(c_542,plain,(
    ! [A_177,F_180,D_178,E_182,C_179,B_181] : k5_enumset1(A_177,A_177,B_181,C_179,D_178,E_182,F_180) = k4_enumset1(A_177,B_181,C_179,D_178,E_182,F_180) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [G_49,I_53,E_47,F_48,D_46,A_43,B_44] : r2_hidden(I_53,k5_enumset1(A_43,B_44,I_53,D_46,E_47,F_48,G_49)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_576,plain,(
    ! [E_188,F_187,A_189,D_185,B_184,C_186] : r2_hidden(B_184,k4_enumset1(A_189,B_184,C_186,D_185,E_188,F_187)) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_48])).

tff(c_580,plain,(
    ! [E_191,D_193,C_194,B_190,A_192] : r2_hidden(A_192,k3_enumset1(A_192,B_190,C_194,D_193,E_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_576])).

tff(c_593,plain,(
    ! [A_202,B_203,C_204,D_205] : r2_hidden(A_202,k2_enumset1(A_202,B_203,C_204,D_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_580])).

tff(c_597,plain,(
    ! [A_206,B_207,C_208] : r2_hidden(A_206,k1_enumset1(A_206,B_207,C_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_593])).

tff(c_600,plain,(
    ! [A_7,B_8] : r2_hidden(A_7,k2_tarski(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_597])).

tff(c_94,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_115,plain,(
    ! [A_62,B_63] : k1_mcart_1(k4_tarski(A_62,B_63)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_124,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_115])).

tff(c_140,plain,(
    ! [A_65,B_66] : k2_mcart_1(k4_tarski(A_65,B_66)) = B_66 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_149,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_140])).

tff(c_92,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_156,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_149,c_92])).

tff(c_157,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_160,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_94])).

tff(c_411,plain,(
    ! [A_160,B_161,C_162] : k2_zfmisc_1(k1_tarski(A_160),k2_tarski(B_161,C_162)) = k2_tarski(k4_tarski(A_160,B_161),k4_tarski(A_160,C_162)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_235,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_244,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_235])).

tff(c_247,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_244])).

tff(c_30,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_248,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_30])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_191,plain,(
    ! [A_71,B_72] :
      ( ~ r1_tarski(A_71,k2_zfmisc_1(A_71,B_72))
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_196,plain,(
    ! [A_34,B_72] :
      ( k1_tarski(A_34) = k1_xboole_0
      | ~ r2_hidden(A_34,k2_zfmisc_1(k1_tarski(A_34),B_72)) ) ),
    inference(resolution,[status(thm)],[c_24,c_191])).

tff(c_290,plain,(
    ! [A_34,B_72] : ~ r2_hidden(A_34,k2_zfmisc_1(k1_tarski(A_34),B_72)) ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_196])).

tff(c_492,plain,(
    ! [A_168,B_169,C_170] : ~ r2_hidden(A_168,k2_tarski(k4_tarski(A_168,B_169),k4_tarski(A_168,C_170))) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_290])).

tff(c_502,plain,(
    ! [C_170] : ~ r2_hidden('#skF_4',k2_tarski('#skF_4',k4_tarski('#skF_4',C_170))) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_492])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_502])).

tff(c_604,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_607,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_94])).

tff(c_751,plain,(
    ! [A_289,B_290,C_291] : k2_zfmisc_1(k2_tarski(A_289,B_290),k1_tarski(C_291)) = k2_tarski(k4_tarski(A_289,C_291),k4_tarski(B_290,C_291)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_678,plain,(
    ! [A_223,B_224] : k5_xboole_0(A_223,k3_xboole_0(A_223,B_224)) = k4_xboole_0(A_223,B_224) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_687,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_678])).

tff(c_690,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_687])).

tff(c_691,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_30])).

tff(c_666,plain,(
    ! [A_219,B_220] :
      ( ~ r1_tarski(A_219,k2_zfmisc_1(B_220,A_219))
      | k1_xboole_0 = A_219 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_671,plain,(
    ! [A_34,B_220] :
      ( k1_tarski(A_34) = k1_xboole_0
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_220,k1_tarski(A_34))) ) ),
    inference(resolution,[status(thm)],[c_24,c_666])).

tff(c_731,plain,(
    ! [A_34,B_220] : ~ r2_hidden(A_34,k2_zfmisc_1(B_220,k1_tarski(A_34))) ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_671])).

tff(c_935,plain,(
    ! [C_310,A_311,B_312] : ~ r2_hidden(C_310,k2_tarski(k4_tarski(A_311,C_310),k4_tarski(B_312,C_310))) ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_731])).

tff(c_945,plain,(
    ! [B_312] : ~ r2_hidden('#skF_3',k2_tarski('#skF_3',k4_tarski(B_312,'#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_935])).

tff(c_1019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.53  
% 3.41/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.54  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.41/1.54  
% 3.41/1.54  %Foreground sorts:
% 3.41/1.54  
% 3.41/1.54  
% 3.41/1.54  %Background operators:
% 3.41/1.54  
% 3.41/1.54  
% 3.41/1.54  %Foreground operators:
% 3.41/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.41/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.41/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.41/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.41/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.41/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.41/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.54  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.41/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.41/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.41/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.54  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.41/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.41/1.54  
% 3.56/1.57  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.56/1.57  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.56/1.57  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.56/1.57  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.56/1.57  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.56/1.57  tff(f_91, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_enumset1)).
% 3.56/1.57  tff(f_107, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.56/1.57  tff(f_97, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.56/1.57  tff(f_64, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.56/1.57  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.56/1.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.56/1.57  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.56/1.57  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.56/1.57  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.56/1.57  tff(f_55, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.56/1.57  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.57  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.57  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.56/1.57  tff(c_16, plain, (![C_18, B_17, A_16, D_19, E_20]: (k4_enumset1(A_16, A_16, B_17, C_18, D_19, E_20)=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.57  tff(c_954, plain, (![C_315, B_317, E_318, F_316, D_314, A_313]: (k5_enumset1(A_313, A_313, B_317, C_315, D_314, E_318, F_316)=k4_enumset1(A_313, B_317, C_315, D_314, E_318, F_316))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.57  tff(c_50, plain, (![G_49, I_53, E_47, F_48, D_46, C_45, A_43]: (r2_hidden(I_53, k5_enumset1(A_43, I_53, C_45, D_46, E_47, F_48, G_49)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.57  tff(c_992, plain, (![A_326, B_323, D_322, F_321, E_325, C_324]: (r2_hidden(A_326, k4_enumset1(A_326, B_323, C_324, D_322, E_325, F_321)))), inference(superposition, [status(thm), theory('equality')], [c_954, c_50])).
% 3.56/1.57  tff(c_1005, plain, (![C_338, B_334, A_336, E_335, D_337]: (r2_hidden(A_336, k3_enumset1(A_336, B_334, C_338, D_337, E_335)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_992])).
% 3.56/1.57  tff(c_1009, plain, (![A_339, B_340, C_341, D_342]: (r2_hidden(A_339, k2_enumset1(A_339, B_340, C_341, D_342)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1005])).
% 3.56/1.57  tff(c_1013, plain, (![A_343, B_344, C_345]: (r2_hidden(A_343, k1_enumset1(A_343, B_344, C_345)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1009])).
% 3.56/1.57  tff(c_1016, plain, (![A_7, B_8]: (r2_hidden(A_7, k2_tarski(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1013])).
% 3.56/1.57  tff(c_542, plain, (![A_177, F_180, D_178, E_182, C_179, B_181]: (k5_enumset1(A_177, A_177, B_181, C_179, D_178, E_182, F_180)=k4_enumset1(A_177, B_181, C_179, D_178, E_182, F_180))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.57  tff(c_48, plain, (![G_49, I_53, E_47, F_48, D_46, A_43, B_44]: (r2_hidden(I_53, k5_enumset1(A_43, B_44, I_53, D_46, E_47, F_48, G_49)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.57  tff(c_576, plain, (![E_188, F_187, A_189, D_185, B_184, C_186]: (r2_hidden(B_184, k4_enumset1(A_189, B_184, C_186, D_185, E_188, F_187)))), inference(superposition, [status(thm), theory('equality')], [c_542, c_48])).
% 3.56/1.57  tff(c_580, plain, (![E_191, D_193, C_194, B_190, A_192]: (r2_hidden(A_192, k3_enumset1(A_192, B_190, C_194, D_193, E_191)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_576])).
% 3.56/1.57  tff(c_593, plain, (![A_202, B_203, C_204, D_205]: (r2_hidden(A_202, k2_enumset1(A_202, B_203, C_204, D_205)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_580])).
% 3.56/1.57  tff(c_597, plain, (![A_206, B_207, C_208]: (r2_hidden(A_206, k1_enumset1(A_206, B_207, C_208)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_593])).
% 3.56/1.57  tff(c_600, plain, (![A_7, B_8]: (r2_hidden(A_7, k2_tarski(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_597])).
% 3.56/1.57  tff(c_94, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.57  tff(c_115, plain, (![A_62, B_63]: (k1_mcart_1(k4_tarski(A_62, B_63))=A_62)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.56/1.57  tff(c_124, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_94, c_115])).
% 3.56/1.57  tff(c_140, plain, (![A_65, B_66]: (k2_mcart_1(k4_tarski(A_65, B_66))=B_66)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.56/1.57  tff(c_149, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_94, c_140])).
% 3.56/1.57  tff(c_92, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.57  tff(c_156, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_149, c_92])).
% 3.56/1.57  tff(c_157, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_156])).
% 3.56/1.57  tff(c_160, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_94])).
% 3.56/1.57  tff(c_411, plain, (![A_160, B_161, C_162]: (k2_zfmisc_1(k1_tarski(A_160), k2_tarski(B_161, C_162))=k2_tarski(k4_tarski(A_160, B_161), k4_tarski(A_160, C_162)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.57  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.57  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.56/1.57  tff(c_235, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.57  tff(c_244, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_235])).
% 3.56/1.57  tff(c_247, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_244])).
% 3.56/1.57  tff(c_30, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.57  tff(c_248, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_247, c_30])).
% 3.56/1.57  tff(c_24, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.56/1.57  tff(c_191, plain, (![A_71, B_72]: (~r1_tarski(A_71, k2_zfmisc_1(A_71, B_72)) | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.57  tff(c_196, plain, (![A_34, B_72]: (k1_tarski(A_34)=k1_xboole_0 | ~r2_hidden(A_34, k2_zfmisc_1(k1_tarski(A_34), B_72)))), inference(resolution, [status(thm)], [c_24, c_191])).
% 3.56/1.57  tff(c_290, plain, (![A_34, B_72]: (~r2_hidden(A_34, k2_zfmisc_1(k1_tarski(A_34), B_72)))), inference(negUnitSimplification, [status(thm)], [c_248, c_196])).
% 3.56/1.57  tff(c_492, plain, (![A_168, B_169, C_170]: (~r2_hidden(A_168, k2_tarski(k4_tarski(A_168, B_169), k4_tarski(A_168, C_170))))), inference(superposition, [status(thm), theory('equality')], [c_411, c_290])).
% 3.56/1.57  tff(c_502, plain, (![C_170]: (~r2_hidden('#skF_4', k2_tarski('#skF_4', k4_tarski('#skF_4', C_170))))), inference(superposition, [status(thm), theory('equality')], [c_160, c_492])).
% 3.56/1.57  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_600, c_502])).
% 3.56/1.57  tff(c_604, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_156])).
% 3.56/1.57  tff(c_607, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_604, c_94])).
% 3.56/1.57  tff(c_751, plain, (![A_289, B_290, C_291]: (k2_zfmisc_1(k2_tarski(A_289, B_290), k1_tarski(C_291))=k2_tarski(k4_tarski(A_289, C_291), k4_tarski(B_290, C_291)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.57  tff(c_678, plain, (![A_223, B_224]: (k5_xboole_0(A_223, k3_xboole_0(A_223, B_224))=k4_xboole_0(A_223, B_224))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.57  tff(c_687, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_678])).
% 3.56/1.57  tff(c_690, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_687])).
% 3.56/1.57  tff(c_691, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_690, c_30])).
% 3.56/1.57  tff(c_666, plain, (![A_219, B_220]: (~r1_tarski(A_219, k2_zfmisc_1(B_220, A_219)) | k1_xboole_0=A_219)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.57  tff(c_671, plain, (![A_34, B_220]: (k1_tarski(A_34)=k1_xboole_0 | ~r2_hidden(A_34, k2_zfmisc_1(B_220, k1_tarski(A_34))))), inference(resolution, [status(thm)], [c_24, c_666])).
% 3.56/1.57  tff(c_731, plain, (![A_34, B_220]: (~r2_hidden(A_34, k2_zfmisc_1(B_220, k1_tarski(A_34))))), inference(negUnitSimplification, [status(thm)], [c_691, c_671])).
% 3.56/1.57  tff(c_935, plain, (![C_310, A_311, B_312]: (~r2_hidden(C_310, k2_tarski(k4_tarski(A_311, C_310), k4_tarski(B_312, C_310))))), inference(superposition, [status(thm), theory('equality')], [c_751, c_731])).
% 3.56/1.57  tff(c_945, plain, (![B_312]: (~r2_hidden('#skF_3', k2_tarski('#skF_3', k4_tarski(B_312, '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_607, c_935])).
% 3.56/1.57  tff(c_1019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1016, c_945])).
% 3.56/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.57  
% 3.56/1.57  Inference rules
% 3.56/1.57  ----------------------
% 3.56/1.57  #Ref     : 0
% 3.56/1.57  #Sup     : 225
% 3.56/1.57  #Fact    : 0
% 3.56/1.57  #Define  : 0
% 3.56/1.57  #Split   : 1
% 3.56/1.57  #Chain   : 0
% 3.56/1.57  #Close   : 0
% 3.56/1.57  
% 3.56/1.57  Ordering : KBO
% 3.56/1.57  
% 3.56/1.57  Simplification rules
% 3.56/1.57  ----------------------
% 3.56/1.57  #Subsume      : 23
% 3.56/1.57  #Demod        : 61
% 3.56/1.57  #Tautology    : 118
% 3.56/1.57  #SimpNegUnit  : 16
% 3.56/1.57  #BackRed      : 9
% 3.56/1.57  
% 3.56/1.57  #Partial instantiations: 0
% 3.56/1.57  #Strategies tried      : 1
% 3.56/1.57  
% 3.56/1.57  Timing (in seconds)
% 3.56/1.57  ----------------------
% 3.56/1.58  Preprocessing        : 0.36
% 3.56/1.58  Parsing              : 0.18
% 3.56/1.58  CNF conversion       : 0.03
% 3.56/1.58  Main loop            : 0.41
% 3.56/1.58  Inferencing          : 0.15
% 3.56/1.58  Reduction            : 0.12
% 3.56/1.58  Demodulation         : 0.09
% 3.56/1.58  BG Simplification    : 0.03
% 3.56/1.58  Subsumption          : 0.09
% 3.56/1.58  Abstraction          : 0.03
% 3.56/1.58  MUC search           : 0.00
% 3.56/1.58  Cooper               : 0.00
% 3.56/1.58  Total                : 0.83
% 3.56/1.58  Index Insertion      : 0.00
% 3.56/1.58  Index Deletion       : 0.00
% 3.56/1.58  Index Matching       : 0.00
% 3.56/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
