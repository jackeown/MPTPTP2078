%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:01 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 159 expanded)
%              Number of leaves         :   44 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 175 expanded)
%              Number of equality atoms :   71 ( 114 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_80,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_100,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_100,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_76,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_229,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    ! [E_35,B_30,C_31] : r2_hidden(E_35,k1_enumset1(E_35,B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_247,plain,(
    ! [A_93,B_94] : r2_hidden(A_93,k2_tarski(A_93,B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_58])).

tff(c_256,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_247])).

tff(c_40,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_183,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_479,plain,(
    ! [A_114,B_115] : k2_xboole_0(A_114,k4_xboole_0(B_115,A_114)) = k2_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_502,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = k2_xboole_0('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_479])).

tff(c_508,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_502])).

tff(c_541,plain,(
    ! [D_119,B_120,A_121] :
      ( ~ r2_hidden(D_119,B_120)
      | r2_hidden(D_119,k2_xboole_0(A_121,B_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_572,plain,(
    ! [D_125] :
      ( ~ r2_hidden(D_125,k1_tarski('#skF_7'))
      | r2_hidden(D_125,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_541])).

tff(c_576,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_256,c_572])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_576])).

tff(c_581,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_46,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,(
    ! [A_68] : k3_tarski(k1_tarski(A_68)) = A_68 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_637,plain,(
    ! [A_138,B_139] : k3_tarski(k2_tarski(A_138,B_139)) = k2_xboole_0(A_138,B_139) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_652,plain,(
    ! [A_36] : k3_tarski(k1_tarski(A_36)) = k2_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_637])).

tff(c_655,plain,(
    ! [A_36] : k2_xboole_0(A_36,A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_652])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1302,plain,(
    ! [A_184,B_185] : k5_xboole_0(k5_xboole_0(A_184,B_185),k2_xboole_0(A_184,B_185)) = k3_xboole_0(A_184,B_185) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1384,plain,(
    ! [A_24] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_24,A_24)) = k3_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1302])).

tff(c_1395,plain,(
    ! [A_24] : k5_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_22,c_1384])).

tff(c_1072,plain,(
    ! [A_177,B_178,C_179] : k5_xboole_0(k5_xboole_0(A_177,B_178),C_179) = k5_xboole_0(A_177,k5_xboole_0(B_178,C_179)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1122,plain,(
    ! [A_24,C_179] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_179)) = k5_xboole_0(k1_xboole_0,C_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1072])).

tff(c_1731,plain,(
    ! [A_24,C_179] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_179)) = C_179 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_1122])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_703,plain,(
    ! [A_146,B_147] :
      ( k2_xboole_0(A_146,B_147) = B_147
      | ~ r1_tarski(A_146,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_707,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(k1_tarski(A_64),B_65) = B_65
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_92,c_703])).

tff(c_2799,plain,(
    ! [A_255,B_256] : k5_xboole_0(k5_xboole_0(A_255,B_256),k2_xboole_0(B_256,A_255)) = k3_xboole_0(B_256,A_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1302])).

tff(c_2907,plain,(
    ! [B_65,A_64] :
      ( k5_xboole_0(k5_xboole_0(B_65,k1_tarski(A_64)),B_65) = k3_xboole_0(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_2799])).

tff(c_2974,plain,(
    ! [A_264,B_265] :
      ( k3_xboole_0(k1_tarski(A_264),B_265) = k1_tarski(A_264)
      | ~ r2_hidden(A_264,B_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1731,c_2,c_2907])).

tff(c_36,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2993,plain,(
    ! [A_264,B_265] :
      ( k5_xboole_0(k1_tarski(A_264),k1_tarski(A_264)) = k4_xboole_0(k1_tarski(A_264),B_265)
      | ~ r2_hidden(A_264,B_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2974,c_36])).

tff(c_3021,plain,(
    ! [A_266,B_267] :
      ( k4_xboole_0(k1_tarski(A_266),B_267) = k1_xboole_0
      | ~ r2_hidden(A_266,B_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2993])).

tff(c_582,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_102,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_686,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_102])).

tff(c_3050,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3021,c_686])).

tff(c_3077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_3050])).

tff(c_3078,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_3198,plain,(
    ! [A_290,B_291] : k3_tarski(k2_tarski(A_290,B_291)) = k2_xboole_0(A_290,B_291) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3213,plain,(
    ! [A_36] : k3_tarski(k1_tarski(A_36)) = k2_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_3198])).

tff(c_3216,plain,(
    ! [A_36] : k2_xboole_0(A_36,A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3213])).

tff(c_3546,plain,(
    ! [A_322,B_323] : k5_xboole_0(k5_xboole_0(A_322,B_323),k2_xboole_0(A_322,B_323)) = k3_xboole_0(A_322,B_323) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3600,plain,(
    ! [A_24] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_24,A_24)) = k3_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3546])).

tff(c_3610,plain,(
    ! [A_24] : k5_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3216,c_22,c_3600])).

tff(c_3710,plain,(
    ! [A_326,B_327,C_328] : k5_xboole_0(k5_xboole_0(A_326,B_327),C_328) = k5_xboole_0(A_326,k5_xboole_0(B_327,C_328)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3787,plain,(
    ! [A_24,C_328] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_328)) = k5_xboole_0(k1_xboole_0,C_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3710])).

tff(c_3906,plain,(
    ! [A_335,C_336] : k5_xboole_0(A_335,k5_xboole_0(A_335,C_336)) = C_336 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_3787])).

tff(c_3961,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3906])).

tff(c_3236,plain,(
    ! [A_293,B_294] :
      ( k2_xboole_0(A_293,B_294) = B_294
      | ~ r1_tarski(A_293,B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3240,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(k1_tarski(A_64),B_65) = B_65
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_92,c_3236])).

tff(c_5122,plain,(
    ! [A_400,B_401] : k5_xboole_0(k2_xboole_0(A_400,B_401),k5_xboole_0(A_400,B_401)) = k3_xboole_0(A_400,B_401) ),
    inference(superposition,[status(thm),theory(equality)],[c_3546,c_2])).

tff(c_5209,plain,(
    ! [B_65,A_64] :
      ( k5_xboole_0(B_65,k5_xboole_0(k1_tarski(A_64),B_65)) = k3_xboole_0(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3240,c_5122])).

tff(c_5266,plain,(
    ! [A_409,B_410] :
      ( k3_xboole_0(k1_tarski(A_409),B_410) = k1_tarski(A_409)
      | ~ r2_hidden(A_409,B_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3961,c_5209])).

tff(c_5289,plain,(
    ! [A_409,B_410] :
      ( k5_xboole_0(k1_tarski(A_409),k1_tarski(A_409)) = k4_xboole_0(k1_tarski(A_409),B_410)
      | ~ r2_hidden(A_409,B_410) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5266,c_36])).

tff(c_5321,plain,(
    ! [A_411,B_412] :
      ( k4_xboole_0(k1_tarski(A_411),B_412) = k1_xboole_0
      | ~ r2_hidden(A_411,B_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5289])).

tff(c_3079,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_98,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3180,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3079,c_98])).

tff(c_5350,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5321,c_3180])).

tff(c_5374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3078,c_5350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.07  
% 5.32/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.39/2.07  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 5.39/2.07  
% 5.39/2.07  %Foreground sorts:
% 5.39/2.07  
% 5.39/2.07  
% 5.39/2.07  %Background operators:
% 5.39/2.07  
% 5.39/2.07  
% 5.39/2.07  %Foreground operators:
% 5.39/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.39/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.39/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.39/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.39/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.39/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.39/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.39/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.39/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.39/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.39/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.39/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.39/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.39/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.39/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.39/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.39/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.39/2.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.39/2.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.39/2.07  tff('#skF_8', type, '#skF_8': $i).
% 5.39/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.39/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.39/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.39/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.39/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.39/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.39/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.39/2.07  
% 5.39/2.09  tff(f_105, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 5.39/2.09  tff(f_80, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.39/2.09  tff(f_82, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.39/2.09  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.39/2.09  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.39/2.09  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.39/2.09  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.39/2.09  tff(f_59, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.39/2.09  tff(f_100, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 5.39/2.09  tff(f_98, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.39/2.09  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.39/2.09  tff(f_61, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.39/2.09  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.39/2.09  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.39/2.09  tff(f_96, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.39/2.09  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.39/2.09  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.39/2.09  tff(c_100, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.39/2.09  tff(c_148, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_100])).
% 5.39/2.09  tff(c_76, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.39/2.09  tff(c_229, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.39/2.09  tff(c_58, plain, (![E_35, B_30, C_31]: (r2_hidden(E_35, k1_enumset1(E_35, B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.39/2.09  tff(c_247, plain, (![A_93, B_94]: (r2_hidden(A_93, k2_tarski(A_93, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_229, c_58])).
% 5.39/2.09  tff(c_256, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_247])).
% 5.39/2.09  tff(c_40, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.39/2.09  tff(c_104, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.39/2.09  tff(c_183, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_104])).
% 5.39/2.09  tff(c_479, plain, (![A_114, B_115]: (k2_xboole_0(A_114, k4_xboole_0(B_115, A_114))=k2_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.09  tff(c_502, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))=k2_xboole_0('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_183, c_479])).
% 5.39/2.09  tff(c_508, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_502])).
% 5.39/2.09  tff(c_541, plain, (![D_119, B_120, A_121]: (~r2_hidden(D_119, B_120) | r2_hidden(D_119, k2_xboole_0(A_121, B_120)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.39/2.09  tff(c_572, plain, (![D_125]: (~r2_hidden(D_125, k1_tarski('#skF_7')) | r2_hidden(D_125, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_508, c_541])).
% 5.39/2.09  tff(c_576, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_256, c_572])).
% 5.39/2.09  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_576])).
% 5.39/2.09  tff(c_581, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_104])).
% 5.39/2.09  tff(c_46, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.39/2.09  tff(c_96, plain, (![A_68]: (k3_tarski(k1_tarski(A_68))=A_68)), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.39/2.09  tff(c_637, plain, (![A_138, B_139]: (k3_tarski(k2_tarski(A_138, B_139))=k2_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.39/2.09  tff(c_652, plain, (![A_36]: (k3_tarski(k1_tarski(A_36))=k2_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_76, c_637])).
% 5.39/2.09  tff(c_655, plain, (![A_36]: (k2_xboole_0(A_36, A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_652])).
% 5.39/2.09  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.39/2.09  tff(c_1302, plain, (![A_184, B_185]: (k5_xboole_0(k5_xboole_0(A_184, B_185), k2_xboole_0(A_184, B_185))=k3_xboole_0(A_184, B_185))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.39/2.09  tff(c_1384, plain, (![A_24]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_24, A_24))=k3_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1302])).
% 5.39/2.09  tff(c_1395, plain, (![A_24]: (k5_xboole_0(k1_xboole_0, A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_655, c_22, c_1384])).
% 5.39/2.09  tff(c_1072, plain, (![A_177, B_178, C_179]: (k5_xboole_0(k5_xboole_0(A_177, B_178), C_179)=k5_xboole_0(A_177, k5_xboole_0(B_178, C_179)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.39/2.09  tff(c_1122, plain, (![A_24, C_179]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_179))=k5_xboole_0(k1_xboole_0, C_179))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1072])).
% 5.39/2.09  tff(c_1731, plain, (![A_24, C_179]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_179))=C_179)), inference(demodulation, [status(thm), theory('equality')], [c_1395, c_1122])).
% 5.39/2.09  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.39/2.09  tff(c_92, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.09  tff(c_703, plain, (![A_146, B_147]: (k2_xboole_0(A_146, B_147)=B_147 | ~r1_tarski(A_146, B_147))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.39/2.09  tff(c_707, plain, (![A_64, B_65]: (k2_xboole_0(k1_tarski(A_64), B_65)=B_65 | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_92, c_703])).
% 5.39/2.09  tff(c_2799, plain, (![A_255, B_256]: (k5_xboole_0(k5_xboole_0(A_255, B_256), k2_xboole_0(B_256, A_255))=k3_xboole_0(B_256, A_255))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1302])).
% 5.39/2.09  tff(c_2907, plain, (![B_65, A_64]: (k5_xboole_0(k5_xboole_0(B_65, k1_tarski(A_64)), B_65)=k3_xboole_0(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_707, c_2799])).
% 5.39/2.09  tff(c_2974, plain, (![A_264, B_265]: (k3_xboole_0(k1_tarski(A_264), B_265)=k1_tarski(A_264) | ~r2_hidden(A_264, B_265))), inference(demodulation, [status(thm), theory('equality')], [c_1731, c_2, c_2907])).
% 5.39/2.09  tff(c_36, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.39/2.09  tff(c_2993, plain, (![A_264, B_265]: (k5_xboole_0(k1_tarski(A_264), k1_tarski(A_264))=k4_xboole_0(k1_tarski(A_264), B_265) | ~r2_hidden(A_264, B_265))), inference(superposition, [status(thm), theory('equality')], [c_2974, c_36])).
% 5.39/2.09  tff(c_3021, plain, (![A_266, B_267]: (k4_xboole_0(k1_tarski(A_266), B_267)=k1_xboole_0 | ~r2_hidden(A_266, B_267))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2993])).
% 5.39/2.09  tff(c_582, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_104])).
% 5.39/2.09  tff(c_102, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.39/2.09  tff(c_686, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_582, c_102])).
% 5.39/2.09  tff(c_3050, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3021, c_686])).
% 5.39/2.09  tff(c_3077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_581, c_3050])).
% 5.39/2.09  tff(c_3078, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_100])).
% 5.39/2.09  tff(c_3198, plain, (![A_290, B_291]: (k3_tarski(k2_tarski(A_290, B_291))=k2_xboole_0(A_290, B_291))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.39/2.09  tff(c_3213, plain, (![A_36]: (k3_tarski(k1_tarski(A_36))=k2_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_76, c_3198])).
% 5.39/2.09  tff(c_3216, plain, (![A_36]: (k2_xboole_0(A_36, A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3213])).
% 5.39/2.09  tff(c_3546, plain, (![A_322, B_323]: (k5_xboole_0(k5_xboole_0(A_322, B_323), k2_xboole_0(A_322, B_323))=k3_xboole_0(A_322, B_323))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.39/2.09  tff(c_3600, plain, (![A_24]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_24, A_24))=k3_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3546])).
% 5.39/2.09  tff(c_3610, plain, (![A_24]: (k5_xboole_0(k1_xboole_0, A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_3216, c_22, c_3600])).
% 5.39/2.09  tff(c_3710, plain, (![A_326, B_327, C_328]: (k5_xboole_0(k5_xboole_0(A_326, B_327), C_328)=k5_xboole_0(A_326, k5_xboole_0(B_327, C_328)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.39/2.09  tff(c_3787, plain, (![A_24, C_328]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_328))=k5_xboole_0(k1_xboole_0, C_328))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3710])).
% 5.39/2.09  tff(c_3906, plain, (![A_335, C_336]: (k5_xboole_0(A_335, k5_xboole_0(A_335, C_336))=C_336)), inference(demodulation, [status(thm), theory('equality')], [c_3610, c_3787])).
% 5.39/2.09  tff(c_3961, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3906])).
% 5.39/2.09  tff(c_3236, plain, (![A_293, B_294]: (k2_xboole_0(A_293, B_294)=B_294 | ~r1_tarski(A_293, B_294))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.39/2.09  tff(c_3240, plain, (![A_64, B_65]: (k2_xboole_0(k1_tarski(A_64), B_65)=B_65 | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_92, c_3236])).
% 5.39/2.09  tff(c_5122, plain, (![A_400, B_401]: (k5_xboole_0(k2_xboole_0(A_400, B_401), k5_xboole_0(A_400, B_401))=k3_xboole_0(A_400, B_401))), inference(superposition, [status(thm), theory('equality')], [c_3546, c_2])).
% 5.39/2.09  tff(c_5209, plain, (![B_65, A_64]: (k5_xboole_0(B_65, k5_xboole_0(k1_tarski(A_64), B_65))=k3_xboole_0(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_3240, c_5122])).
% 5.39/2.09  tff(c_5266, plain, (![A_409, B_410]: (k3_xboole_0(k1_tarski(A_409), B_410)=k1_tarski(A_409) | ~r2_hidden(A_409, B_410))), inference(demodulation, [status(thm), theory('equality')], [c_3961, c_5209])).
% 5.39/2.09  tff(c_5289, plain, (![A_409, B_410]: (k5_xboole_0(k1_tarski(A_409), k1_tarski(A_409))=k4_xboole_0(k1_tarski(A_409), B_410) | ~r2_hidden(A_409, B_410))), inference(superposition, [status(thm), theory('equality')], [c_5266, c_36])).
% 5.39/2.09  tff(c_5321, plain, (![A_411, B_412]: (k4_xboole_0(k1_tarski(A_411), B_412)=k1_xboole_0 | ~r2_hidden(A_411, B_412))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5289])).
% 5.39/2.09  tff(c_3079, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_100])).
% 5.39/2.09  tff(c_98, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.39/2.09  tff(c_3180, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3079, c_98])).
% 5.39/2.09  tff(c_5350, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5321, c_3180])).
% 5.39/2.09  tff(c_5374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3078, c_5350])).
% 5.39/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.39/2.09  
% 5.39/2.09  Inference rules
% 5.39/2.09  ----------------------
% 5.39/2.09  #Ref     : 0
% 5.39/2.09  #Sup     : 1316
% 5.39/2.09  #Fact    : 0
% 5.39/2.09  #Define  : 0
% 5.39/2.09  #Split   : 2
% 5.39/2.09  #Chain   : 0
% 5.39/2.09  #Close   : 0
% 5.39/2.09  
% 5.39/2.09  Ordering : KBO
% 5.39/2.09  
% 5.39/2.09  Simplification rules
% 5.39/2.09  ----------------------
% 5.39/2.09  #Subsume      : 116
% 5.39/2.09  #Demod        : 661
% 5.39/2.09  #Tautology    : 765
% 5.39/2.09  #SimpNegUnit  : 2
% 5.39/2.09  #BackRed      : 3
% 5.39/2.09  
% 5.39/2.09  #Partial instantiations: 0
% 5.39/2.09  #Strategies tried      : 1
% 5.39/2.09  
% 5.39/2.09  Timing (in seconds)
% 5.39/2.09  ----------------------
% 5.39/2.09  Preprocessing        : 0.38
% 5.39/2.09  Parsing              : 0.20
% 5.39/2.09  CNF conversion       : 0.03
% 5.39/2.09  Main loop            : 0.89
% 5.39/2.09  Inferencing          : 0.29
% 5.39/2.09  Reduction            : 0.36
% 5.39/2.09  Demodulation         : 0.29
% 5.39/2.09  BG Simplification    : 0.04
% 5.39/2.09  Subsumption          : 0.13
% 5.39/2.09  Abstraction          : 0.05
% 5.39/2.09  MUC search           : 0.00
% 5.39/2.09  Cooper               : 0.00
% 5.39/2.09  Total                : 1.30
% 5.39/2.09  Index Insertion      : 0.00
% 5.39/2.09  Index Deletion       : 0.00
% 5.39/2.09  Index Matching       : 0.00
% 5.39/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
