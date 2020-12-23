%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:16 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 165 expanded)
%              Number of leaves         :   45 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 190 expanded)
%              Number of equality atoms :   71 ( 152 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

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

tff(c_1123,plain,(
    ! [C_331,D_335,B_333,A_334,E_332] : k4_enumset1(A_334,A_334,B_333,C_331,D_335,E_332) = k3_enumset1(A_334,B_333,C_331,D_335,E_332) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [B_49,H_57,A_48,D_51,E_52,C_50] : r2_hidden(H_57,k4_enumset1(A_48,B_49,C_50,D_51,E_52,H_57)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1158,plain,(
    ! [C_338,E_342,A_341,D_339,B_340] : r2_hidden(E_342,k3_enumset1(A_341,B_340,C_338,D_339,E_342)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_44])).

tff(c_1171,plain,(
    ! [D_349,A_350,B_351,C_352] : r2_hidden(D_349,k2_enumset1(A_350,B_351,C_352,D_349)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1158])).

tff(c_1175,plain,(
    ! [C_353,A_354,B_355] : r2_hidden(C_353,k1_enumset1(A_354,B_355,C_353)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1171])).

tff(c_1179,plain,(
    ! [B_356,A_357] : r2_hidden(B_356,k2_tarski(A_357,B_356)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1175])).

tff(c_1188,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1179])).

tff(c_393,plain,(
    ! [C_147,E_148,D_151,B_149,A_150] : k4_enumset1(A_150,A_150,B_149,C_147,D_151,E_148) = k3_enumset1(A_150,B_149,C_147,D_151,E_148) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [B_49,F_53,H_57,A_48,D_51,E_52] : r2_hidden(H_57,k4_enumset1(A_48,B_49,H_57,D_51,E_52,F_53)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_420,plain,(
    ! [E_155,A_154,B_156,D_152,C_153] : r2_hidden(B_156,k3_enumset1(A_154,B_156,C_153,D_152,E_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_50])).

tff(c_424,plain,(
    ! [A_157,B_158,C_159,D_160] : r2_hidden(A_157,k2_enumset1(A_157,B_158,C_159,D_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_420])).

tff(c_481,plain,(
    ! [A_164,B_165,C_166] : r2_hidden(A_164,k1_enumset1(A_164,B_165,C_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_424])).

tff(c_485,plain,(
    ! [A_167,B_168] : r2_hidden(A_167,k2_tarski(A_167,B_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_481])).

tff(c_491,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_485])).

tff(c_92,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,(
    ! [A_65,B_66] : k1_mcart_1(k4_tarski(A_65,B_66)) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_115,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_106])).

tff(c_131,plain,(
    ! [A_68,B_69] : k2_mcart_1(k4_tarski(A_68,B_69)) = B_69 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_140,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_131])).

tff(c_90,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_163,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_140,c_90])).

tff(c_164,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_167,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_92])).

tff(c_493,plain,(
    ! [A_170,B_171,C_172] : k2_zfmisc_1(k1_tarski(A_170),k2_tarski(B_171,C_172)) = k2_tarski(k4_tarski(A_170,B_171),k4_tarski(A_170,C_172)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_531,plain,(
    ! [A_170,C_172] : k2_zfmisc_1(k1_tarski(A_170),k2_tarski(C_172,C_172)) = k1_tarski(k4_tarski(A_170,C_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_10])).

tff(c_634,plain,(
    ! [A_226,C_227] : k2_zfmisc_1(k1_tarski(A_226),k1_tarski(C_227)) = k1_tarski(k4_tarski(A_226,C_227)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_531])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_301,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_313,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_301])).

tff(c_320,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_313])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_316,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_301])).

tff(c_345,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_316])).

tff(c_34,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_346,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_34])).

tff(c_283,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_tarski(A_86),B_87)
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( ~ r1_tarski(A_41,k2_zfmisc_1(A_41,B_42))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_288,plain,(
    ! [A_86,B_42] :
      ( k1_tarski(A_86) = k1_xboole_0
      | ~ r2_hidden(A_86,k2_zfmisc_1(k1_tarski(A_86),B_42)) ) ),
    inference(resolution,[status(thm)],[c_283,c_32])).

tff(c_389,plain,(
    ! [A_86,B_42] : ~ r2_hidden(A_86,k2_zfmisc_1(k1_tarski(A_86),B_42)) ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_288])).

tff(c_695,plain,(
    ! [A_237,C_238] : ~ r2_hidden(A_237,k1_tarski(k4_tarski(A_237,C_238))) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_389])).

tff(c_698,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_695])).

tff(c_701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_698])).

tff(c_702,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_705,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_92])).

tff(c_923,plain,(
    ! [A_312,B_313,C_314] : k2_zfmisc_1(k1_tarski(A_312),k2_tarski(B_313,C_314)) = k2_tarski(k4_tarski(A_312,B_313),k4_tarski(A_312,C_314)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_951,plain,(
    ! [A_312,C_314] : k2_zfmisc_1(k1_tarski(A_312),k2_tarski(C_314,C_314)) = k1_tarski(k4_tarski(A_312,C_314)) ),
    inference(superposition,[status(thm),theory(equality)],[c_923,c_10])).

tff(c_976,plain,(
    ! [A_315,C_316] : k2_zfmisc_1(k1_tarski(A_315),k1_tarski(C_316)) = k1_tarski(k4_tarski(A_315,C_316)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_951])).

tff(c_835,plain,(
    ! [A_258,B_259] : k5_xboole_0(A_258,k3_xboole_0(A_258,B_259)) = k4_xboole_0(A_258,B_259) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_847,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_835])).

tff(c_854,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_847])).

tff(c_850,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_835])).

tff(c_863,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_850])).

tff(c_864,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_34])).

tff(c_727,plain,(
    ! [A_241,B_242] :
      ( r1_tarski(k1_tarski(A_241),B_242)
      | ~ r2_hidden(A_241,B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_41,B_42] :
      ( ~ r1_tarski(A_41,k2_zfmisc_1(B_42,A_41))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_732,plain,(
    ! [A_241,B_42] :
      ( k1_tarski(A_241) = k1_xboole_0
      | ~ r2_hidden(A_241,k2_zfmisc_1(B_42,k1_tarski(A_241))) ) ),
    inference(resolution,[status(thm)],[c_727,c_30])).

tff(c_910,plain,(
    ! [A_241,B_42] : ~ r2_hidden(A_241,k2_zfmisc_1(B_42,k1_tarski(A_241))) ),
    inference(negUnitSimplification,[status(thm)],[c_864,c_732])).

tff(c_1072,plain,(
    ! [C_322,A_323] : ~ r2_hidden(C_322,k1_tarski(k4_tarski(A_323,C_322))) ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_910])).

tff(c_1075,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_1072])).

tff(c_1191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1188,c_1075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.65  
% 3.27/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.65  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.65  
% 3.27/1.65  %Foreground sorts:
% 3.27/1.65  
% 3.27/1.65  
% 3.27/1.65  %Background operators:
% 3.27/1.65  
% 3.27/1.65  
% 3.27/1.65  %Foreground operators:
% 3.27/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.27/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.27/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.65  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.27/1.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.27/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.65  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.27/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.27/1.65  
% 3.56/1.67  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.56/1.67  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.56/1.67  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.56/1.67  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.56/1.67  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.56/1.67  tff(f_92, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 3.56/1.67  tff(f_108, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.56/1.67  tff(f_98, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.56/1.67  tff(f_68, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.56/1.67  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.56/1.67  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.56/1.67  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.56/1.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.56/1.67  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.56/1.67  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.56/1.67  tff(f_59, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.56/1.67  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.67  tff(c_12, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.67  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.56/1.67  tff(c_16, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.67  tff(c_1123, plain, (![C_331, D_335, B_333, A_334, E_332]: (k4_enumset1(A_334, A_334, B_333, C_331, D_335, E_332)=k3_enumset1(A_334, B_333, C_331, D_335, E_332))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.67  tff(c_44, plain, (![B_49, H_57, A_48, D_51, E_52, C_50]: (r2_hidden(H_57, k4_enumset1(A_48, B_49, C_50, D_51, E_52, H_57)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.67  tff(c_1158, plain, (![C_338, E_342, A_341, D_339, B_340]: (r2_hidden(E_342, k3_enumset1(A_341, B_340, C_338, D_339, E_342)))), inference(superposition, [status(thm), theory('equality')], [c_1123, c_44])).
% 3.56/1.67  tff(c_1171, plain, (![D_349, A_350, B_351, C_352]: (r2_hidden(D_349, k2_enumset1(A_350, B_351, C_352, D_349)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1158])).
% 3.56/1.67  tff(c_1175, plain, (![C_353, A_354, B_355]: (r2_hidden(C_353, k1_enumset1(A_354, B_355, C_353)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1171])).
% 3.56/1.67  tff(c_1179, plain, (![B_356, A_357]: (r2_hidden(B_356, k2_tarski(A_357, B_356)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1175])).
% 3.56/1.67  tff(c_1188, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1179])).
% 3.56/1.67  tff(c_393, plain, (![C_147, E_148, D_151, B_149, A_150]: (k4_enumset1(A_150, A_150, B_149, C_147, D_151, E_148)=k3_enumset1(A_150, B_149, C_147, D_151, E_148))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.67  tff(c_50, plain, (![B_49, F_53, H_57, A_48, D_51, E_52]: (r2_hidden(H_57, k4_enumset1(A_48, B_49, H_57, D_51, E_52, F_53)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.67  tff(c_420, plain, (![E_155, A_154, B_156, D_152, C_153]: (r2_hidden(B_156, k3_enumset1(A_154, B_156, C_153, D_152, E_155)))), inference(superposition, [status(thm), theory('equality')], [c_393, c_50])).
% 3.56/1.67  tff(c_424, plain, (![A_157, B_158, C_159, D_160]: (r2_hidden(A_157, k2_enumset1(A_157, B_158, C_159, D_160)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_420])).
% 3.56/1.67  tff(c_481, plain, (![A_164, B_165, C_166]: (r2_hidden(A_164, k1_enumset1(A_164, B_165, C_166)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_424])).
% 3.56/1.67  tff(c_485, plain, (![A_167, B_168]: (r2_hidden(A_167, k2_tarski(A_167, B_168)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_481])).
% 3.56/1.67  tff(c_491, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_485])).
% 3.56/1.67  tff(c_92, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.67  tff(c_106, plain, (![A_65, B_66]: (k1_mcart_1(k4_tarski(A_65, B_66))=A_65)), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.56/1.67  tff(c_115, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_92, c_106])).
% 3.56/1.67  tff(c_131, plain, (![A_68, B_69]: (k2_mcart_1(k4_tarski(A_68, B_69))=B_69)), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.56/1.67  tff(c_140, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_92, c_131])).
% 3.56/1.67  tff(c_90, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.67  tff(c_163, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_140, c_90])).
% 3.56/1.67  tff(c_164, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_163])).
% 3.56/1.67  tff(c_167, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_92])).
% 3.56/1.67  tff(c_493, plain, (![A_170, B_171, C_172]: (k2_zfmisc_1(k1_tarski(A_170), k2_tarski(B_171, C_172))=k2_tarski(k4_tarski(A_170, B_171), k4_tarski(A_170, C_172)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.67  tff(c_531, plain, (![A_170, C_172]: (k2_zfmisc_1(k1_tarski(A_170), k2_tarski(C_172, C_172))=k1_tarski(k4_tarski(A_170, C_172)))), inference(superposition, [status(thm), theory('equality')], [c_493, c_10])).
% 3.56/1.67  tff(c_634, plain, (![A_226, C_227]: (k2_zfmisc_1(k1_tarski(A_226), k1_tarski(C_227))=k1_tarski(k4_tarski(A_226, C_227)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_531])).
% 3.56/1.67  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.67  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.67  tff(c_301, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.67  tff(c_313, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_301])).
% 3.56/1.67  tff(c_320, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_313])).
% 3.56/1.67  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.56/1.67  tff(c_316, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_301])).
% 3.56/1.67  tff(c_345, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_320, c_316])).
% 3.56/1.67  tff(c_34, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.67  tff(c_346, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_34])).
% 3.56/1.67  tff(c_283, plain, (![A_86, B_87]: (r1_tarski(k1_tarski(A_86), B_87) | ~r2_hidden(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.67  tff(c_32, plain, (![A_41, B_42]: (~r1_tarski(A_41, k2_zfmisc_1(A_41, B_42)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.56/1.67  tff(c_288, plain, (![A_86, B_42]: (k1_tarski(A_86)=k1_xboole_0 | ~r2_hidden(A_86, k2_zfmisc_1(k1_tarski(A_86), B_42)))), inference(resolution, [status(thm)], [c_283, c_32])).
% 3.56/1.67  tff(c_389, plain, (![A_86, B_42]: (~r2_hidden(A_86, k2_zfmisc_1(k1_tarski(A_86), B_42)))), inference(negUnitSimplification, [status(thm)], [c_346, c_288])).
% 3.56/1.67  tff(c_695, plain, (![A_237, C_238]: (~r2_hidden(A_237, k1_tarski(k4_tarski(A_237, C_238))))), inference(superposition, [status(thm), theory('equality')], [c_634, c_389])).
% 3.56/1.67  tff(c_698, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_695])).
% 3.56/1.67  tff(c_701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_491, c_698])).
% 3.56/1.67  tff(c_702, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_163])).
% 3.56/1.67  tff(c_705, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_702, c_92])).
% 3.56/1.67  tff(c_923, plain, (![A_312, B_313, C_314]: (k2_zfmisc_1(k1_tarski(A_312), k2_tarski(B_313, C_314))=k2_tarski(k4_tarski(A_312, B_313), k4_tarski(A_312, C_314)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.67  tff(c_951, plain, (![A_312, C_314]: (k2_zfmisc_1(k1_tarski(A_312), k2_tarski(C_314, C_314))=k1_tarski(k4_tarski(A_312, C_314)))), inference(superposition, [status(thm), theory('equality')], [c_923, c_10])).
% 3.56/1.67  tff(c_976, plain, (![A_315, C_316]: (k2_zfmisc_1(k1_tarski(A_315), k1_tarski(C_316))=k1_tarski(k4_tarski(A_315, C_316)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_951])).
% 3.56/1.67  tff(c_835, plain, (![A_258, B_259]: (k5_xboole_0(A_258, k3_xboole_0(A_258, B_259))=k4_xboole_0(A_258, B_259))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.67  tff(c_847, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_835])).
% 3.56/1.67  tff(c_854, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_847])).
% 3.56/1.67  tff(c_850, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_835])).
% 3.56/1.67  tff(c_863, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_854, c_850])).
% 3.56/1.67  tff(c_864, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_863, c_34])).
% 3.56/1.67  tff(c_727, plain, (![A_241, B_242]: (r1_tarski(k1_tarski(A_241), B_242) | ~r2_hidden(A_241, B_242))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.67  tff(c_30, plain, (![A_41, B_42]: (~r1_tarski(A_41, k2_zfmisc_1(B_42, A_41)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.56/1.67  tff(c_732, plain, (![A_241, B_42]: (k1_tarski(A_241)=k1_xboole_0 | ~r2_hidden(A_241, k2_zfmisc_1(B_42, k1_tarski(A_241))))), inference(resolution, [status(thm)], [c_727, c_30])).
% 3.56/1.67  tff(c_910, plain, (![A_241, B_42]: (~r2_hidden(A_241, k2_zfmisc_1(B_42, k1_tarski(A_241))))), inference(negUnitSimplification, [status(thm)], [c_864, c_732])).
% 3.56/1.67  tff(c_1072, plain, (![C_322, A_323]: (~r2_hidden(C_322, k1_tarski(k4_tarski(A_323, C_322))))), inference(superposition, [status(thm), theory('equality')], [c_976, c_910])).
% 3.56/1.67  tff(c_1075, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_705, c_1072])).
% 3.56/1.67  tff(c_1191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1188, c_1075])).
% 3.56/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.67  
% 3.56/1.67  Inference rules
% 3.56/1.67  ----------------------
% 3.56/1.67  #Ref     : 0
% 3.56/1.67  #Sup     : 269
% 3.56/1.67  #Fact    : 0
% 3.56/1.67  #Define  : 0
% 3.56/1.67  #Split   : 1
% 3.56/1.67  #Chain   : 0
% 3.56/1.67  #Close   : 0
% 3.56/1.67  
% 3.56/1.67  Ordering : KBO
% 3.56/1.67  
% 3.56/1.67  Simplification rules
% 3.56/1.67  ----------------------
% 3.56/1.67  #Subsume      : 9
% 3.56/1.67  #Demod        : 63
% 3.56/1.67  #Tautology    : 155
% 3.56/1.67  #SimpNegUnit  : 14
% 3.56/1.67  #BackRed      : 8
% 3.56/1.67  
% 3.56/1.67  #Partial instantiations: 0
% 3.56/1.67  #Strategies tried      : 1
% 3.56/1.67  
% 3.56/1.67  Timing (in seconds)
% 3.56/1.67  ----------------------
% 3.56/1.68  Preprocessing        : 0.40
% 3.56/1.68  Parsing              : 0.18
% 3.56/1.68  CNF conversion       : 0.03
% 3.56/1.68  Main loop            : 0.47
% 3.56/1.68  Inferencing          : 0.17
% 3.56/1.68  Reduction            : 0.15
% 3.56/1.68  Demodulation         : 0.11
% 3.56/1.68  BG Simplification    : 0.03
% 3.56/1.68  Subsumption          : 0.09
% 3.56/1.68  Abstraction          : 0.04
% 3.56/1.68  MUC search           : 0.00
% 3.56/1.68  Cooper               : 0.00
% 3.56/1.68  Total                : 0.92
% 3.56/1.68  Index Insertion      : 0.00
% 3.56/1.68  Index Deletion       : 0.00
% 3.56/1.68  Index Matching       : 0.00
% 3.56/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
