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
% DateTime   : Thu Dec  3 10:09:14 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 284 expanded)
%              Number of leaves         :   45 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 429 expanded)
%              Number of equality atoms :   56 ( 290 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_9 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_3 > #skF_8 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_119,axiom,(
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

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_660,plain,(
    ! [A_240,B_241,C_242] :
      ( ~ r1_xboole_0(A_240,B_241)
      | ~ r2_hidden(C_242,B_241)
      | ~ r2_hidden(C_242,A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_663,plain,(
    ! [C_242] : ~ r2_hidden(C_242,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_660])).

tff(c_14,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_719,plain,(
    ! [D_278,C_275,A_276,B_277,E_279] : k4_enumset1(A_276,A_276,B_277,C_275,D_278,E_279) = k3_enumset1(A_276,B_277,C_275,D_278,E_279) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_64,plain,(
    ! [B_77,A_76,C_78,E_80,H_85,D_79] : r2_hidden(H_85,k4_enumset1(A_76,B_77,C_78,D_79,E_80,H_85)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_856,plain,(
    ! [A_330,C_328,B_329,D_331,E_332] : r2_hidden(E_332,k3_enumset1(A_330,B_329,C_328,D_331,E_332)) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_64])).

tff(c_928,plain,(
    ! [D_336,A_337,B_338,C_339] : r2_hidden(D_336,k2_enumset1(A_337,B_338,C_339,D_336)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_856])).

tff(c_932,plain,(
    ! [C_340,A_341,B_342] : r2_hidden(C_340,k1_enumset1(A_341,B_342,C_340)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_928])).

tff(c_935,plain,(
    ! [B_9,A_8] : r2_hidden(B_9,k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_932])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ! [B_77,A_76,C_78,E_80,H_85,F_81] : r2_hidden(H_85,k4_enumset1(A_76,B_77,C_78,H_85,E_80,F_81)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_746,plain,(
    ! [B_281,A_282,D_283,C_280,E_284] : r2_hidden(C_280,k3_enumset1(A_282,B_281,C_280,D_283,E_284)) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_68])).

tff(c_750,plain,(
    ! [B_285,A_286,C_287,D_288] : r2_hidden(B_285,k2_enumset1(A_286,B_285,C_287,D_288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_746])).

tff(c_754,plain,(
    ! [A_289,B_290,C_291] : r2_hidden(A_289,k1_enumset1(A_289,B_290,C_291)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_750])).

tff(c_758,plain,(
    ! [A_292,B_293] : r2_hidden(A_292,k2_tarski(A_292,B_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_754])).

tff(c_761,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_758])).

tff(c_227,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ r1_xboole_0(A_131,B_132)
      | ~ r2_hidden(C_133,B_132)
      | ~ r2_hidden(C_133,A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_230,plain,(
    ! [C_133] : ~ r2_hidden(C_133,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_227])).

tff(c_513,plain,(
    ! [D_192,A_190,B_191,E_193,C_189] : k4_enumset1(A_190,A_190,B_191,C_189,D_192,E_193) = k3_enumset1(A_190,B_191,C_189,D_192,E_193) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    ! [B_77,A_76,E_80,H_85,F_81,D_79] : r2_hidden(H_85,k4_enumset1(A_76,B_77,H_85,D_79,E_80,F_81)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_540,plain,(
    ! [A_195,D_196,E_198,C_194,B_197] : r2_hidden(B_197,k3_enumset1(A_195,B_197,C_194,D_196,E_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_70])).

tff(c_544,plain,(
    ! [A_199,B_200,C_201,D_202] : r2_hidden(A_199,k2_enumset1(A_199,B_200,C_201,D_202)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_540])).

tff(c_548,plain,(
    ! [A_203,B_204,C_205] : r2_hidden(A_203,k1_enumset1(A_203,B_204,C_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_544])).

tff(c_553,plain,(
    ! [A_206,B_207] : r2_hidden(A_206,k2_tarski(A_206,B_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_548])).

tff(c_562,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_553])).

tff(c_110,plain,(
    k4_tarski('#skF_11','#skF_12') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_115,plain,(
    ! [A_90,B_91] : k1_mcart_1(k4_tarski(A_90,B_91)) = A_90 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_124,plain,(
    k1_mcart_1('#skF_10') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_115])).

tff(c_131,plain,(
    ! [A_92,B_93] : k2_mcart_1(k4_tarski(A_92,B_93)) = B_93 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_140,plain,(
    k2_mcart_1('#skF_10') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_131])).

tff(c_108,plain,
    ( k2_mcart_1('#skF_10') = '#skF_10'
    | k1_mcart_1('#skF_10') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_162,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_140,c_108])).

tff(c_163,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_165,plain,(
    k4_tarski('#skF_10','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_110])).

tff(c_277,plain,(
    ! [A_163,B_164,C_165] : k2_zfmisc_1(k1_tarski(A_163),k2_tarski(B_164,C_165)) = k2_tarski(k4_tarski(A_163,B_164),k4_tarski(A_163,C_165)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_299,plain,(
    ! [A_163,C_165] : k2_zfmisc_1(k1_tarski(A_163),k2_tarski(C_165,C_165)) = k1_tarski(k4_tarski(A_163,C_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_12])).

tff(c_323,plain,(
    ! [A_166,C_167] : k2_zfmisc_1(k1_tarski(A_166),k1_tarski(C_167)) = k1_tarski(k4_tarski(A_166,C_167)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_299])).

tff(c_52,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tarski(A_69),B_70)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_192,plain,(
    ! [A_100,B_101] :
      ( ~ r1_tarski(A_100,k2_zfmisc_1(A_100,B_101))
      | k1_xboole_0 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_197,plain,(
    ! [A_69,B_101] :
      ( k1_tarski(A_69) = k1_xboole_0
      | ~ r2_hidden(A_69,k2_zfmisc_1(k1_tarski(A_69),B_101)) ) ),
    inference(resolution,[status(thm)],[c_52,c_192])).

tff(c_371,plain,(
    ! [A_174,C_175] :
      ( k1_tarski(A_174) = k1_xboole_0
      | ~ r2_hidden(A_174,k1_tarski(k4_tarski(A_174,C_175))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_197])).

tff(c_374,plain,
    ( k1_tarski('#skF_10') = k1_xboole_0
    | ~ r2_hidden('#skF_10',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_371])).

tff(c_375,plain,(
    ~ r2_hidden('#skF_10',k1_tarski('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_375])).

tff(c_566,plain,(
    k1_tarski('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_567,plain,(
    r2_hidden('#skF_10',k1_tarski('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_596,plain,(
    r2_hidden('#skF_10',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_567])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_596])).

tff(c_598,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_602,plain,(
    k4_tarski('#skF_11','#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_110])).

tff(c_821,plain,(
    ! [E_307,F_308,A_309,B_310] :
      ( r2_hidden(k4_tarski(E_307,F_308),k2_zfmisc_1(A_309,B_310))
      | ~ r2_hidden(F_308,B_310)
      | ~ r2_hidden(E_307,A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_947,plain,(
    ! [A_345,B_346] :
      ( r2_hidden('#skF_12',k2_zfmisc_1(A_345,B_346))
      | ~ r2_hidden('#skF_12',B_346)
      | ~ r2_hidden('#skF_11',A_345) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_821])).

tff(c_640,plain,(
    ! [A_216,B_217] :
      ( r1_tarski(k1_tarski(A_216),B_217)
      | ~ r2_hidden(A_216,B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    ! [A_71,B_72] :
      ( ~ r1_tarski(A_71,k2_zfmisc_1(B_72,A_71))
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_654,plain,(
    ! [A_216,B_72] :
      ( k1_tarski(A_216) = k1_xboole_0
      | ~ r2_hidden(A_216,k2_zfmisc_1(B_72,k1_tarski(A_216))) ) ),
    inference(resolution,[status(thm)],[c_640,c_54])).

tff(c_951,plain,(
    ! [A_345] :
      ( k1_tarski('#skF_12') = k1_xboole_0
      | ~ r2_hidden('#skF_12',k1_tarski('#skF_12'))
      | ~ r2_hidden('#skF_11',A_345) ) ),
    inference(resolution,[status(thm)],[c_947,c_654])).

tff(c_964,plain,(
    ! [A_345] :
      ( k1_tarski('#skF_12') = k1_xboole_0
      | ~ r2_hidden('#skF_11',A_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_951])).

tff(c_967,plain,(
    ! [A_347] : ~ r2_hidden('#skF_11',A_347) ),
    inference(splitLeft,[status(thm)],[c_964])).

tff(c_1032,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_935,c_967])).

tff(c_1033,plain,(
    k1_tarski('#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_964])).

tff(c_1040,plain,(
    r2_hidden('#skF_12',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_761])).

tff(c_1059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_663,c_1040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n010.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 11:28:14 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.50  
% 3.33/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_9 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_3 > #skF_8 > #skF_1 > #skF_12
% 3.33/1.51  
% 3.33/1.51  %Foreground sorts:
% 3.33/1.51  
% 3.33/1.51  
% 3.33/1.51  %Background operators:
% 3.33/1.51  
% 3.33/1.51  
% 3.33/1.51  %Foreground operators:
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.51  tff('#skF_11', type, '#skF_11': $i).
% 3.33/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.33/1.51  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.33/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.33/1.51  tff('#skF_10', type, '#skF_10': $i).
% 3.33/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.33/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.33/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.33/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.33/1.51  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.33/1.51  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.33/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.51  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.33/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.51  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.33/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.51  tff('#skF_12', type, '#skF_12': $i).
% 3.33/1.51  
% 3.33/1.52  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.33/1.52  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.33/1.52  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.33/1.52  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.33/1.52  tff(f_63, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.33/1.52  tff(f_65, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.33/1.52  tff(f_119, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.33/1.52  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.33/1.52  tff(f_133, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.33/1.52  tff(f_123, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.33/1.52  tff(f_95, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.33/1.52  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.33/1.52  tff(f_91, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.33/1.52  tff(f_81, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.33/1.52  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.33/1.52  tff(c_660, plain, (![A_240, B_241, C_242]: (~r1_xboole_0(A_240, B_241) | ~r2_hidden(C_242, B_241) | ~r2_hidden(C_242, A_240))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.52  tff(c_663, plain, (![C_242]: (~r2_hidden(C_242, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_660])).
% 3.33/1.52  tff(c_14, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.33/1.52  tff(c_16, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.52  tff(c_18, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.33/1.52  tff(c_719, plain, (![D_278, C_275, A_276, B_277, E_279]: (k4_enumset1(A_276, A_276, B_277, C_275, D_278, E_279)=k3_enumset1(A_276, B_277, C_275, D_278, E_279))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.33/1.52  tff(c_64, plain, (![B_77, A_76, C_78, E_80, H_85, D_79]: (r2_hidden(H_85, k4_enumset1(A_76, B_77, C_78, D_79, E_80, H_85)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.33/1.52  tff(c_856, plain, (![A_330, C_328, B_329, D_331, E_332]: (r2_hidden(E_332, k3_enumset1(A_330, B_329, C_328, D_331, E_332)))), inference(superposition, [status(thm), theory('equality')], [c_719, c_64])).
% 3.33/1.52  tff(c_928, plain, (![D_336, A_337, B_338, C_339]: (r2_hidden(D_336, k2_enumset1(A_337, B_338, C_339, D_336)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_856])).
% 3.33/1.52  tff(c_932, plain, (![C_340, A_341, B_342]: (r2_hidden(C_340, k1_enumset1(A_341, B_342, C_340)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_928])).
% 3.33/1.52  tff(c_935, plain, (![B_9, A_8]: (r2_hidden(B_9, k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_932])).
% 3.33/1.52  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.52  tff(c_68, plain, (![B_77, A_76, C_78, E_80, H_85, F_81]: (r2_hidden(H_85, k4_enumset1(A_76, B_77, C_78, H_85, E_80, F_81)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.33/1.52  tff(c_746, plain, (![B_281, A_282, D_283, C_280, E_284]: (r2_hidden(C_280, k3_enumset1(A_282, B_281, C_280, D_283, E_284)))), inference(superposition, [status(thm), theory('equality')], [c_719, c_68])).
% 3.33/1.52  tff(c_750, plain, (![B_285, A_286, C_287, D_288]: (r2_hidden(B_285, k2_enumset1(A_286, B_285, C_287, D_288)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_746])).
% 3.33/1.52  tff(c_754, plain, (![A_289, B_290, C_291]: (r2_hidden(A_289, k1_enumset1(A_289, B_290, C_291)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_750])).
% 3.33/1.52  tff(c_758, plain, (![A_292, B_293]: (r2_hidden(A_292, k2_tarski(A_292, B_293)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_754])).
% 3.33/1.52  tff(c_761, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_758])).
% 3.33/1.52  tff(c_227, plain, (![A_131, B_132, C_133]: (~r1_xboole_0(A_131, B_132) | ~r2_hidden(C_133, B_132) | ~r2_hidden(C_133, A_131))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.52  tff(c_230, plain, (![C_133]: (~r2_hidden(C_133, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_227])).
% 3.33/1.52  tff(c_513, plain, (![D_192, A_190, B_191, E_193, C_189]: (k4_enumset1(A_190, A_190, B_191, C_189, D_192, E_193)=k3_enumset1(A_190, B_191, C_189, D_192, E_193))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.33/1.52  tff(c_70, plain, (![B_77, A_76, E_80, H_85, F_81, D_79]: (r2_hidden(H_85, k4_enumset1(A_76, B_77, H_85, D_79, E_80, F_81)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.33/1.52  tff(c_540, plain, (![A_195, D_196, E_198, C_194, B_197]: (r2_hidden(B_197, k3_enumset1(A_195, B_197, C_194, D_196, E_198)))), inference(superposition, [status(thm), theory('equality')], [c_513, c_70])).
% 3.33/1.52  tff(c_544, plain, (![A_199, B_200, C_201, D_202]: (r2_hidden(A_199, k2_enumset1(A_199, B_200, C_201, D_202)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_540])).
% 3.33/1.52  tff(c_548, plain, (![A_203, B_204, C_205]: (r2_hidden(A_203, k1_enumset1(A_203, B_204, C_205)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_544])).
% 3.33/1.52  tff(c_553, plain, (![A_206, B_207]: (r2_hidden(A_206, k2_tarski(A_206, B_207)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_548])).
% 3.33/1.52  tff(c_562, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_553])).
% 3.33/1.52  tff(c_110, plain, (k4_tarski('#skF_11', '#skF_12')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.33/1.52  tff(c_115, plain, (![A_90, B_91]: (k1_mcart_1(k4_tarski(A_90, B_91))=A_90)), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.33/1.52  tff(c_124, plain, (k1_mcart_1('#skF_10')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_110, c_115])).
% 3.33/1.52  tff(c_131, plain, (![A_92, B_93]: (k2_mcart_1(k4_tarski(A_92, B_93))=B_93)), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.33/1.52  tff(c_140, plain, (k2_mcart_1('#skF_10')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_110, c_131])).
% 3.33/1.52  tff(c_108, plain, (k2_mcart_1('#skF_10')='#skF_10' | k1_mcart_1('#skF_10')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.33/1.52  tff(c_162, plain, ('#skF_10'='#skF_12' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_140, c_108])).
% 3.33/1.52  tff(c_163, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_162])).
% 3.33/1.52  tff(c_165, plain, (k4_tarski('#skF_10', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_110])).
% 3.33/1.52  tff(c_277, plain, (![A_163, B_164, C_165]: (k2_zfmisc_1(k1_tarski(A_163), k2_tarski(B_164, C_165))=k2_tarski(k4_tarski(A_163, B_164), k4_tarski(A_163, C_165)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.33/1.52  tff(c_299, plain, (![A_163, C_165]: (k2_zfmisc_1(k1_tarski(A_163), k2_tarski(C_165, C_165))=k1_tarski(k4_tarski(A_163, C_165)))), inference(superposition, [status(thm), theory('equality')], [c_277, c_12])).
% 3.33/1.52  tff(c_323, plain, (![A_166, C_167]: (k2_zfmisc_1(k1_tarski(A_166), k1_tarski(C_167))=k1_tarski(k4_tarski(A_166, C_167)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_299])).
% 3.33/1.52  tff(c_52, plain, (![A_69, B_70]: (r1_tarski(k1_tarski(A_69), B_70) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.33/1.52  tff(c_192, plain, (![A_100, B_101]: (~r1_tarski(A_100, k2_zfmisc_1(A_100, B_101)) | k1_xboole_0=A_100)), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.33/1.52  tff(c_197, plain, (![A_69, B_101]: (k1_tarski(A_69)=k1_xboole_0 | ~r2_hidden(A_69, k2_zfmisc_1(k1_tarski(A_69), B_101)))), inference(resolution, [status(thm)], [c_52, c_192])).
% 3.33/1.52  tff(c_371, plain, (![A_174, C_175]: (k1_tarski(A_174)=k1_xboole_0 | ~r2_hidden(A_174, k1_tarski(k4_tarski(A_174, C_175))))), inference(superposition, [status(thm), theory('equality')], [c_323, c_197])).
% 3.33/1.52  tff(c_374, plain, (k1_tarski('#skF_10')=k1_xboole_0 | ~r2_hidden('#skF_10', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_371])).
% 3.33/1.52  tff(c_375, plain, (~r2_hidden('#skF_10', k1_tarski('#skF_10'))), inference(splitLeft, [status(thm)], [c_374])).
% 3.33/1.52  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_562, c_375])).
% 3.33/1.52  tff(c_566, plain, (k1_tarski('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_374])).
% 3.33/1.52  tff(c_567, plain, (r2_hidden('#skF_10', k1_tarski('#skF_10'))), inference(splitRight, [status(thm)], [c_374])).
% 3.33/1.52  tff(c_596, plain, (r2_hidden('#skF_10', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_566, c_567])).
% 3.33/1.52  tff(c_597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_596])).
% 3.33/1.52  tff(c_598, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_162])).
% 3.33/1.52  tff(c_602, plain, (k4_tarski('#skF_11', '#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_598, c_110])).
% 3.33/1.52  tff(c_821, plain, (![E_307, F_308, A_309, B_310]: (r2_hidden(k4_tarski(E_307, F_308), k2_zfmisc_1(A_309, B_310)) | ~r2_hidden(F_308, B_310) | ~r2_hidden(E_307, A_309))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.33/1.52  tff(c_947, plain, (![A_345, B_346]: (r2_hidden('#skF_12', k2_zfmisc_1(A_345, B_346)) | ~r2_hidden('#skF_12', B_346) | ~r2_hidden('#skF_11', A_345))), inference(superposition, [status(thm), theory('equality')], [c_602, c_821])).
% 3.33/1.52  tff(c_640, plain, (![A_216, B_217]: (r1_tarski(k1_tarski(A_216), B_217) | ~r2_hidden(A_216, B_217))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.33/1.52  tff(c_54, plain, (![A_71, B_72]: (~r1_tarski(A_71, k2_zfmisc_1(B_72, A_71)) | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.33/1.52  tff(c_654, plain, (![A_216, B_72]: (k1_tarski(A_216)=k1_xboole_0 | ~r2_hidden(A_216, k2_zfmisc_1(B_72, k1_tarski(A_216))))), inference(resolution, [status(thm)], [c_640, c_54])).
% 3.33/1.52  tff(c_951, plain, (![A_345]: (k1_tarski('#skF_12')=k1_xboole_0 | ~r2_hidden('#skF_12', k1_tarski('#skF_12')) | ~r2_hidden('#skF_11', A_345))), inference(resolution, [status(thm)], [c_947, c_654])).
% 3.33/1.52  tff(c_964, plain, (![A_345]: (k1_tarski('#skF_12')=k1_xboole_0 | ~r2_hidden('#skF_11', A_345))), inference(demodulation, [status(thm), theory('equality')], [c_761, c_951])).
% 3.33/1.52  tff(c_967, plain, (![A_347]: (~r2_hidden('#skF_11', A_347))), inference(splitLeft, [status(thm)], [c_964])).
% 3.33/1.52  tff(c_1032, plain, $false, inference(resolution, [status(thm)], [c_935, c_967])).
% 3.33/1.52  tff(c_1033, plain, (k1_tarski('#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_964])).
% 3.33/1.52  tff(c_1040, plain, (r2_hidden('#skF_12', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1033, c_761])).
% 3.33/1.52  tff(c_1059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_663, c_1040])).
% 3.33/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.52  
% 3.33/1.52  Inference rules
% 3.33/1.52  ----------------------
% 3.33/1.52  #Ref     : 0
% 3.33/1.53  #Sup     : 240
% 3.33/1.53  #Fact    : 0
% 3.33/1.53  #Define  : 0
% 3.33/1.53  #Split   : 8
% 3.33/1.53  #Chain   : 0
% 3.33/1.53  #Close   : 0
% 3.33/1.53  
% 3.33/1.53  Ordering : KBO
% 3.33/1.53  
% 3.33/1.53  Simplification rules
% 3.33/1.53  ----------------------
% 3.33/1.53  #Subsume      : 16
% 3.33/1.53  #Demod        : 52
% 3.33/1.53  #Tautology    : 91
% 3.33/1.53  #SimpNegUnit  : 2
% 3.33/1.53  #BackRed      : 7
% 3.33/1.53  
% 3.33/1.53  #Partial instantiations: 0
% 3.33/1.53  #Strategies tried      : 1
% 3.33/1.53  
% 3.33/1.53  Timing (in seconds)
% 3.33/1.53  ----------------------
% 3.33/1.53  Preprocessing        : 0.36
% 3.33/1.53  Parsing              : 0.17
% 3.33/1.53  CNF conversion       : 0.03
% 3.33/1.53  Main loop            : 0.39
% 3.33/1.53  Inferencing          : 0.14
% 3.33/1.53  Reduction            : 0.12
% 3.33/1.53  Demodulation         : 0.08
% 3.33/1.53  BG Simplification    : 0.03
% 3.33/1.53  Subsumption          : 0.08
% 3.33/1.53  Abstraction          : 0.03
% 3.33/1.53  MUC search           : 0.00
% 3.33/1.53  Cooper               : 0.00
% 3.33/1.53  Total                : 0.79
% 3.33/1.53  Index Insertion      : 0.00
% 3.33/1.53  Index Deletion       : 0.00
% 3.33/1.53  Index Matching       : 0.00
% 3.33/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
