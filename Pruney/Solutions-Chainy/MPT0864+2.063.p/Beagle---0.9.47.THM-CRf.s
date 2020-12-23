%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:17 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 157 expanded)
%              Number of leaves         :   42 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 184 expanded)
%              Number of equality atoms :   67 ( 146 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_88,axiom,(
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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_949,plain,(
    ! [E_301,B_304,C_303,D_302,A_305] : k4_enumset1(A_305,A_305,B_304,C_303,D_302,E_301) = k3_enumset1(A_305,B_304,C_303,D_302,E_301) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [H_52,E_47,F_48,D_46,C_45,A_43] : r2_hidden(H_52,k4_enumset1(A_43,H_52,C_45,D_46,E_47,F_48)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1091,plain,(
    ! [A_325,C_327,D_323,E_326,B_324] : r2_hidden(A_325,k3_enumset1(A_325,B_324,C_327,D_323,E_326)) ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_48])).

tff(c_1095,plain,(
    ! [A_328,B_329,C_330,D_331] : r2_hidden(A_328,k2_enumset1(A_328,B_329,C_330,D_331)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1091])).

tff(c_1099,plain,(
    ! [A_332,B_333,C_334] : r2_hidden(A_332,k1_enumset1(A_332,B_333,C_334)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1095])).

tff(c_1103,plain,(
    ! [A_335,B_336] : r2_hidden(A_335,k2_tarski(A_335,B_336)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1099])).

tff(c_1112,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1103])).

tff(c_369,plain,(
    ! [A_143,C_141,B_142,E_139,D_140] : k4_enumset1(A_143,A_143,B_142,C_141,D_140,E_139) = k3_enumset1(A_143,B_142,C_141,D_140,E_139) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [H_52,E_47,F_48,C_45,A_43,B_44] : r2_hidden(H_52,k4_enumset1(A_43,B_44,C_45,H_52,E_47,F_48)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_396,plain,(
    ! [C_148,A_144,D_147,E_146,B_145] : r2_hidden(C_148,k3_enumset1(A_144,B_145,C_148,D_147,E_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_44])).

tff(c_400,plain,(
    ! [B_149,A_150,C_151,D_152] : r2_hidden(B_149,k2_enumset1(A_150,B_149,C_151,D_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_396])).

tff(c_460,plain,(
    ! [A_156,B_157,C_158] : r2_hidden(A_156,k1_enumset1(A_156,B_157,C_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_400])).

tff(c_464,plain,(
    ! [A_159,B_160] : r2_hidden(A_159,k2_tarski(A_159,B_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_460])).

tff(c_470,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_464])).

tff(c_88,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_100,plain,(
    ! [A_60,B_61] : k1_mcart_1(k4_tarski(A_60,B_61)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_109,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_100])).

tff(c_125,plain,(
    ! [A_63,B_64] : k2_mcart_1(k4_tarski(A_63,B_64)) = B_64 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_134,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_125])).

tff(c_86,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_141,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_134,c_86])).

tff(c_142,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_145,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_88])).

tff(c_472,plain,(
    ! [A_162,B_163,C_164] : k2_zfmisc_1(k1_tarski(A_162),k2_tarski(B_163,C_164)) = k2_tarski(k4_tarski(A_162,B_163),k4_tarski(A_162,C_164)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_536,plain,(
    ! [A_162,B_163] : k2_zfmisc_1(k1_tarski(A_162),k2_tarski(B_163,B_163)) = k1_tarski(k4_tarski(A_162,B_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_472])).

tff(c_616,plain,(
    ! [A_218,B_219] : k2_zfmisc_1(k1_tarski(A_218),k1_tarski(B_219)) = k1_tarski(k4_tarski(A_218,B_219)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_536])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_239,plain,(
    ! [A_81,B_82] : k3_xboole_0(k1_tarski(A_81),k2_tarski(A_81,B_82)) = k1_tarski(A_81) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_245,plain,(
    ! [A_81,B_82] : k5_xboole_0(k1_tarski(A_81),k1_tarski(A_81)) = k4_xboole_0(k1_tarski(A_81),k2_tarski(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_2])).

tff(c_255,plain,(
    ! [A_83,B_84] : k4_xboole_0(k1_tarski(A_83),k2_tarski(A_83,B_84)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_245])).

tff(c_262,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_255])).

tff(c_30,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_266,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_30])).

tff(c_211,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_tarski(A_75),B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(A_34,k2_zfmisc_1(A_34,B_35))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_221,plain,(
    ! [A_75,B_35] :
      ( k1_tarski(A_75) = k1_xboole_0
      | ~ r2_hidden(A_75,k2_zfmisc_1(k1_tarski(A_75),B_35)) ) ),
    inference(resolution,[status(thm)],[c_211,c_26])).

tff(c_367,plain,(
    ! [A_75,B_35] : ~ r2_hidden(A_75,k2_zfmisc_1(k1_tarski(A_75),B_35)) ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_221])).

tff(c_639,plain,(
    ! [A_220,B_221] : ~ r2_hidden(A_220,k1_tarski(k4_tarski(A_220,B_221))) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_367])).

tff(c_642,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_639])).

tff(c_645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_642])).

tff(c_646,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_650,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_88])).

tff(c_870,plain,(
    ! [A_296,B_297,C_298] : k2_zfmisc_1(k1_tarski(A_296),k2_tarski(B_297,C_298)) = k2_tarski(k4_tarski(A_296,B_297),k4_tarski(A_296,C_298)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_901,plain,(
    ! [A_296,C_298] : k2_zfmisc_1(k1_tarski(A_296),k2_tarski(C_298,C_298)) = k1_tarski(k4_tarski(A_296,C_298)) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_6])).

tff(c_926,plain,(
    ! [A_299,C_300] : k2_zfmisc_1(k1_tarski(A_299),k1_tarski(C_300)) = k1_tarski(k4_tarski(A_299,C_300)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_901])).

tff(c_739,plain,(
    ! [A_238,B_239] : k3_xboole_0(k1_tarski(A_238),k2_tarski(A_238,B_239)) = k1_tarski(A_238) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_756,plain,(
    ! [A_246] : k3_xboole_0(k1_tarski(A_246),k1_tarski(A_246)) = k1_tarski(A_246) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_739])).

tff(c_762,plain,(
    ! [A_246] : k5_xboole_0(k1_tarski(A_246),k1_tarski(A_246)) = k4_xboole_0(k1_tarski(A_246),k1_tarski(A_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_2])).

tff(c_773,plain,(
    ! [A_246] : k4_xboole_0(k1_tarski(A_246),k1_tarski(A_246)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_762])).

tff(c_775,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_30])).

tff(c_22,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_687,plain,(
    ! [A_229,B_230] :
      ( ~ r1_tarski(A_229,k2_zfmisc_1(B_230,A_229))
      | k1_xboole_0 = A_229 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_692,plain,(
    ! [A_32,B_230] :
      ( k1_tarski(A_32) = k1_xboole_0
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_230,k1_tarski(A_32))) ) ),
    inference(resolution,[status(thm)],[c_22,c_687])).

tff(c_857,plain,(
    ! [A_32,B_230] : ~ r2_hidden(A_32,k2_zfmisc_1(B_230,k1_tarski(A_32))) ),
    inference(negUnitSimplification,[status(thm)],[c_775,c_692])).

tff(c_980,plain,(
    ! [C_308,A_309] : ~ r2_hidden(C_308,k1_tarski(k4_tarski(A_309,C_308))) ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_857])).

tff(c_983,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_980])).

tff(c_1115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_983])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.22/1.48  
% 3.22/1.48  %Foreground sorts:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Background operators:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Foreground operators:
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.22/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.48  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.22/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.48  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.22/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.22/1.48  
% 3.22/1.49  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.22/1.49  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.22/1.49  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.22/1.49  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.22/1.49  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.22/1.49  tff(f_88, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.22/1.50  tff(f_104, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.22/1.50  tff(f_94, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.22/1.50  tff(f_64, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.22/1.50  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.22/1.50  tff(f_55, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.22/1.50  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.50  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.22/1.50  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.22/1.50  tff(f_53, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.22/1.50  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.50  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.50  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.50  tff(c_949, plain, (![E_301, B_304, C_303, D_302, A_305]: (k4_enumset1(A_305, A_305, B_304, C_303, D_302, E_301)=k3_enumset1(A_305, B_304, C_303, D_302, E_301))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.50  tff(c_48, plain, (![H_52, E_47, F_48, D_46, C_45, A_43]: (r2_hidden(H_52, k4_enumset1(A_43, H_52, C_45, D_46, E_47, F_48)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.22/1.50  tff(c_1091, plain, (![A_325, C_327, D_323, E_326, B_324]: (r2_hidden(A_325, k3_enumset1(A_325, B_324, C_327, D_323, E_326)))), inference(superposition, [status(thm), theory('equality')], [c_949, c_48])).
% 3.22/1.50  tff(c_1095, plain, (![A_328, B_329, C_330, D_331]: (r2_hidden(A_328, k2_enumset1(A_328, B_329, C_330, D_331)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1091])).
% 3.22/1.50  tff(c_1099, plain, (![A_332, B_333, C_334]: (r2_hidden(A_332, k1_enumset1(A_332, B_333, C_334)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1095])).
% 3.22/1.50  tff(c_1103, plain, (![A_335, B_336]: (r2_hidden(A_335, k2_tarski(A_335, B_336)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1099])).
% 3.22/1.50  tff(c_1112, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1103])).
% 3.22/1.50  tff(c_369, plain, (![A_143, C_141, B_142, E_139, D_140]: (k4_enumset1(A_143, A_143, B_142, C_141, D_140, E_139)=k3_enumset1(A_143, B_142, C_141, D_140, E_139))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.50  tff(c_44, plain, (![H_52, E_47, F_48, C_45, A_43, B_44]: (r2_hidden(H_52, k4_enumset1(A_43, B_44, C_45, H_52, E_47, F_48)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.22/1.50  tff(c_396, plain, (![C_148, A_144, D_147, E_146, B_145]: (r2_hidden(C_148, k3_enumset1(A_144, B_145, C_148, D_147, E_146)))), inference(superposition, [status(thm), theory('equality')], [c_369, c_44])).
% 3.22/1.50  tff(c_400, plain, (![B_149, A_150, C_151, D_152]: (r2_hidden(B_149, k2_enumset1(A_150, B_149, C_151, D_152)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_396])).
% 3.22/1.50  tff(c_460, plain, (![A_156, B_157, C_158]: (r2_hidden(A_156, k1_enumset1(A_156, B_157, C_158)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_400])).
% 3.22/1.50  tff(c_464, plain, (![A_159, B_160]: (r2_hidden(A_159, k2_tarski(A_159, B_160)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_460])).
% 3.22/1.50  tff(c_470, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_464])).
% 3.22/1.50  tff(c_88, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.22/1.50  tff(c_100, plain, (![A_60, B_61]: (k1_mcart_1(k4_tarski(A_60, B_61))=A_60)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_109, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_88, c_100])).
% 3.22/1.50  tff(c_125, plain, (![A_63, B_64]: (k2_mcart_1(k4_tarski(A_63, B_64))=B_64)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_134, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_88, c_125])).
% 3.22/1.50  tff(c_86, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.22/1.50  tff(c_141, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_134, c_86])).
% 3.22/1.50  tff(c_142, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_141])).
% 3.22/1.50  tff(c_145, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_88])).
% 3.22/1.50  tff(c_472, plain, (![A_162, B_163, C_164]: (k2_zfmisc_1(k1_tarski(A_162), k2_tarski(B_163, C_164))=k2_tarski(k4_tarski(A_162, B_163), k4_tarski(A_162, C_164)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.22/1.50  tff(c_536, plain, (![A_162, B_163]: (k2_zfmisc_1(k1_tarski(A_162), k2_tarski(B_163, B_163))=k1_tarski(k4_tarski(A_162, B_163)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_472])).
% 3.22/1.50  tff(c_616, plain, (![A_218, B_219]: (k2_zfmisc_1(k1_tarski(A_218), k1_tarski(B_219))=k1_tarski(k4_tarski(A_218, B_219)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_536])).
% 3.22/1.50  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.50  tff(c_239, plain, (![A_81, B_82]: (k3_xboole_0(k1_tarski(A_81), k2_tarski(A_81, B_82))=k1_tarski(A_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.50  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.50  tff(c_245, plain, (![A_81, B_82]: (k5_xboole_0(k1_tarski(A_81), k1_tarski(A_81))=k4_xboole_0(k1_tarski(A_81), k2_tarski(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_239, c_2])).
% 3.22/1.50  tff(c_255, plain, (![A_83, B_84]: (k4_xboole_0(k1_tarski(A_83), k2_tarski(A_83, B_84))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_245])).
% 3.22/1.50  tff(c_262, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_255])).
% 3.22/1.50  tff(c_30, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.22/1.50  tff(c_266, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_262, c_30])).
% 3.22/1.50  tff(c_211, plain, (![A_75, B_76]: (r1_tarski(k1_tarski(A_75), B_76) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.50  tff(c_26, plain, (![A_34, B_35]: (~r1_tarski(A_34, k2_zfmisc_1(A_34, B_35)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.50  tff(c_221, plain, (![A_75, B_35]: (k1_tarski(A_75)=k1_xboole_0 | ~r2_hidden(A_75, k2_zfmisc_1(k1_tarski(A_75), B_35)))), inference(resolution, [status(thm)], [c_211, c_26])).
% 3.22/1.50  tff(c_367, plain, (![A_75, B_35]: (~r2_hidden(A_75, k2_zfmisc_1(k1_tarski(A_75), B_35)))), inference(negUnitSimplification, [status(thm)], [c_266, c_221])).
% 3.22/1.50  tff(c_639, plain, (![A_220, B_221]: (~r2_hidden(A_220, k1_tarski(k4_tarski(A_220, B_221))))), inference(superposition, [status(thm), theory('equality')], [c_616, c_367])).
% 3.22/1.50  tff(c_642, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_639])).
% 3.22/1.50  tff(c_645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_470, c_642])).
% 3.22/1.50  tff(c_646, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_141])).
% 3.22/1.50  tff(c_650, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_646, c_88])).
% 3.22/1.50  tff(c_870, plain, (![A_296, B_297, C_298]: (k2_zfmisc_1(k1_tarski(A_296), k2_tarski(B_297, C_298))=k2_tarski(k4_tarski(A_296, B_297), k4_tarski(A_296, C_298)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.22/1.50  tff(c_901, plain, (![A_296, C_298]: (k2_zfmisc_1(k1_tarski(A_296), k2_tarski(C_298, C_298))=k1_tarski(k4_tarski(A_296, C_298)))), inference(superposition, [status(thm), theory('equality')], [c_870, c_6])).
% 3.22/1.50  tff(c_926, plain, (![A_299, C_300]: (k2_zfmisc_1(k1_tarski(A_299), k1_tarski(C_300))=k1_tarski(k4_tarski(A_299, C_300)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_901])).
% 3.22/1.50  tff(c_739, plain, (![A_238, B_239]: (k3_xboole_0(k1_tarski(A_238), k2_tarski(A_238, B_239))=k1_tarski(A_238))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.50  tff(c_756, plain, (![A_246]: (k3_xboole_0(k1_tarski(A_246), k1_tarski(A_246))=k1_tarski(A_246))), inference(superposition, [status(thm), theory('equality')], [c_6, c_739])).
% 3.22/1.50  tff(c_762, plain, (![A_246]: (k5_xboole_0(k1_tarski(A_246), k1_tarski(A_246))=k4_xboole_0(k1_tarski(A_246), k1_tarski(A_246)))), inference(superposition, [status(thm), theory('equality')], [c_756, c_2])).
% 3.22/1.50  tff(c_773, plain, (![A_246]: (k4_xboole_0(k1_tarski(A_246), k1_tarski(A_246))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_762])).
% 3.22/1.50  tff(c_775, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_773, c_30])).
% 3.22/1.50  tff(c_22, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.50  tff(c_687, plain, (![A_229, B_230]: (~r1_tarski(A_229, k2_zfmisc_1(B_230, A_229)) | k1_xboole_0=A_229)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.50  tff(c_692, plain, (![A_32, B_230]: (k1_tarski(A_32)=k1_xboole_0 | ~r2_hidden(A_32, k2_zfmisc_1(B_230, k1_tarski(A_32))))), inference(resolution, [status(thm)], [c_22, c_687])).
% 3.22/1.50  tff(c_857, plain, (![A_32, B_230]: (~r2_hidden(A_32, k2_zfmisc_1(B_230, k1_tarski(A_32))))), inference(negUnitSimplification, [status(thm)], [c_775, c_692])).
% 3.22/1.50  tff(c_980, plain, (![C_308, A_309]: (~r2_hidden(C_308, k1_tarski(k4_tarski(A_309, C_308))))), inference(superposition, [status(thm), theory('equality')], [c_926, c_857])).
% 3.22/1.50  tff(c_983, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_650, c_980])).
% 3.22/1.50  tff(c_1115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1112, c_983])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 255
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 1
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 4
% 3.22/1.50  #Demod        : 57
% 3.22/1.50  #Tautology    : 144
% 3.22/1.50  #SimpNegUnit  : 16
% 3.22/1.50  #BackRed      : 8
% 3.22/1.50  
% 3.22/1.50  #Partial instantiations: 0
% 3.22/1.50  #Strategies tried      : 1
% 3.22/1.50  
% 3.22/1.50  Timing (in seconds)
% 3.22/1.50  ----------------------
% 3.22/1.50  Preprocessing        : 0.34
% 3.22/1.50  Parsing              : 0.17
% 3.22/1.50  CNF conversion       : 0.02
% 3.22/1.50  Main loop            : 0.38
% 3.22/1.50  Inferencing          : 0.14
% 3.22/1.50  Reduction            : 0.12
% 3.37/1.50  Demodulation         : 0.08
% 3.37/1.50  BG Simplification    : 0.03
% 3.37/1.50  Subsumption          : 0.07
% 3.37/1.50  Abstraction          : 0.03
% 3.37/1.50  MUC search           : 0.00
% 3.37/1.50  Cooper               : 0.00
% 3.37/1.50  Total                : 0.76
% 3.37/1.50  Index Insertion      : 0.00
% 3.37/1.50  Index Deletion       : 0.00
% 3.37/1.50  Index Matching       : 0.00
% 3.37/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
