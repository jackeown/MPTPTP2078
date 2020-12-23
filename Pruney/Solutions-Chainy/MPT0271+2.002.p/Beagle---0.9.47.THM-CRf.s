%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:01 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 136 expanded)
%              Number of leaves         :   42 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 152 expanded)
%              Number of equality atoms :   60 (  91 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
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

tff(f_56,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_54,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_90,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_167,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_68,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_312,plain,(
    ! [A_92,B_93] : k1_enumset1(A_92,A_92,B_93) = k2_tarski(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [E_35,A_29,B_30] : r2_hidden(E_35,k1_enumset1(A_29,B_30,E_35)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_330,plain,(
    ! [B_94,A_95] : r2_hidden(B_94,k2_tarski(A_95,B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_46])).

tff(c_339,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_330])).

tff(c_30,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_94,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_201,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_465,plain,(
    ! [A_108,B_109] : k2_xboole_0(A_108,k4_xboole_0(B_109,A_108)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_474,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = k2_xboole_0('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_465])).

tff(c_477,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_474])).

tff(c_580,plain,(
    ! [D_117,B_118,A_119] :
      ( ~ r2_hidden(D_117,B_118)
      | r2_hidden(D_117,k2_xboole_0(A_119,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_602,plain,(
    ! [D_120] :
      ( ~ r2_hidden(D_120,k1_tarski('#skF_7'))
      | r2_hidden(D_120,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_580])).

tff(c_606,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_339,c_602])).

tff(c_610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_606])).

tff(c_611,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_38,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_616,plain,(
    ! [B_130,A_131] : k5_xboole_0(B_130,A_131) = k5_xboole_0(A_131,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_632,plain,(
    ! [A_131] : k5_xboole_0(k1_xboole_0,A_131) = A_131 ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_34])).

tff(c_1237,plain,(
    ! [A_178,B_179,C_180] : k5_xboole_0(k5_xboole_0(A_178,B_179),C_180) = k5_xboole_0(A_178,k5_xboole_0(B_179,C_180)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1301,plain,(
    ! [A_24,C_180] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_180)) = k5_xboole_0(k1_xboole_0,C_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1237])).

tff(c_1315,plain,(
    ! [A_181,C_182] : k5_xboole_0(A_181,k5_xboole_0(A_181,C_182)) = C_182 ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_1301])).

tff(c_1358,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1315])).

tff(c_761,plain,(
    ! [A_140,B_141] :
      ( r1_tarski(k1_tarski(A_140),B_141)
      | ~ r2_hidden(A_140,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_765,plain,(
    ! [A_140,B_141] :
      ( k2_xboole_0(k1_tarski(A_140),B_141) = B_141
      | ~ r2_hidden(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_761,c_28])).

tff(c_1556,plain,(
    ! [A_187,B_188] : k5_xboole_0(k5_xboole_0(A_187,B_188),k2_xboole_0(A_187,B_188)) = k3_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1611,plain,(
    ! [A_140,B_141] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_140),B_141),B_141) = k3_xboole_0(k1_tarski(A_140),B_141)
      | ~ r2_hidden(A_140,B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_1556])).

tff(c_2320,plain,(
    ! [A_232,B_233] :
      ( k3_xboole_0(k1_tarski(A_232),B_233) = k1_tarski(A_232)
      | ~ r2_hidden(A_232,B_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_2,c_1611])).

tff(c_26,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2339,plain,(
    ! [A_232,B_233] :
      ( k5_xboole_0(k1_tarski(A_232),k1_tarski(A_232)) = k4_xboole_0(k1_tarski(A_232),B_233)
      | ~ r2_hidden(A_232,B_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2320,c_26])).

tff(c_2367,plain,(
    ! [A_234,B_235] :
      ( k4_xboole_0(k1_tarski(A_234),B_235) = k1_xboole_0
      | ~ r2_hidden(A_234,B_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2339])).

tff(c_612,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_92,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_712,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_92])).

tff(c_2396,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2367,c_712])).

tff(c_2423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_2396])).

tff(c_2424,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2426,plain,(
    ! [B_236,A_237] : k5_xboole_0(B_236,A_237) = k5_xboole_0(A_237,B_236) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2442,plain,(
    ! [A_237] : k5_xboole_0(k1_xboole_0,A_237) = A_237 ),
    inference(superposition,[status(thm),theory(equality)],[c_2426,c_34])).

tff(c_2928,plain,(
    ! [A_289,B_290,C_291] : k5_xboole_0(k5_xboole_0(A_289,B_290),C_291) = k5_xboole_0(A_289,k5_xboole_0(B_290,C_291)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2992,plain,(
    ! [A_24,C_291] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_291)) = k5_xboole_0(k1_xboole_0,C_291) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2928])).

tff(c_3006,plain,(
    ! [A_292,C_293] : k5_xboole_0(A_292,k5_xboole_0(A_292,C_293)) = C_293 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_2992])).

tff(c_3049,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3006])).

tff(c_2637,plain,(
    ! [A_264,B_265] :
      ( r1_tarski(k1_tarski(A_264),B_265)
      | ~ r2_hidden(A_264,B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3655,plain,(
    ! [A_317,B_318] :
      ( k2_xboole_0(k1_tarski(A_317),B_318) = B_318
      | ~ r2_hidden(A_317,B_318) ) ),
    inference(resolution,[status(thm)],[c_2637,c_28])).

tff(c_40,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k2_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3664,plain,(
    ! [A_317,B_318] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_317),B_318),B_318) = k3_xboole_0(k1_tarski(A_317),B_318)
      | ~ r2_hidden(A_317,B_318) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3655,c_40])).

tff(c_4178,plain,(
    ! [A_359,B_360] :
      ( k3_xboole_0(k1_tarski(A_359),B_360) = k1_tarski(A_359)
      | ~ r2_hidden(A_359,B_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3049,c_2,c_3664])).

tff(c_4197,plain,(
    ! [A_359,B_360] :
      ( k5_xboole_0(k1_tarski(A_359),k1_tarski(A_359)) = k4_xboole_0(k1_tarski(A_359),B_360)
      | ~ r2_hidden(A_359,B_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4178,c_26])).

tff(c_4225,plain,(
    ! [A_361,B_362] :
      ( k4_xboole_0(k1_tarski(A_361),B_362) = k1_xboole_0
      | ~ r2_hidden(A_361,B_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4197])).

tff(c_2425,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2522,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_88])).

tff(c_4254,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4225,c_2522])).

tff(c_4278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_4254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:37:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.80  
% 4.37/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.80  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 4.37/1.80  
% 4.37/1.80  %Foreground sorts:
% 4.37/1.80  
% 4.37/1.80  
% 4.37/1.80  %Background operators:
% 4.37/1.80  
% 4.37/1.80  
% 4.37/1.80  %Foreground operators:
% 4.37/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.37/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.37/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.37/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.37/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.37/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.37/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.37/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.37/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.37/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.37/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.37/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.37/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.37/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.80  
% 4.51/1.82  tff(f_100, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 4.51/1.82  tff(f_77, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.51/1.82  tff(f_79, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.51/1.82  tff(f_75, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.51/1.82  tff(f_48, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.51/1.82  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.51/1.82  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.51/1.82  tff(f_56, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.51/1.82  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.51/1.82  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.51/1.82  tff(f_54, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.51/1.82  tff(f_93, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.51/1.82  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.51/1.82  tff(f_58, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.51/1.82  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.51/1.82  tff(c_90, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.51/1.82  tff(c_167, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 4.51/1.82  tff(c_68, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.82  tff(c_312, plain, (![A_92, B_93]: (k1_enumset1(A_92, A_92, B_93)=k2_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.51/1.82  tff(c_46, plain, (![E_35, A_29, B_30]: (r2_hidden(E_35, k1_enumset1(A_29, B_30, E_35)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.82  tff(c_330, plain, (![B_94, A_95]: (r2_hidden(B_94, k2_tarski(A_95, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_312, c_46])).
% 4.51/1.82  tff(c_339, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_330])).
% 4.51/1.82  tff(c_30, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.51/1.82  tff(c_94, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.51/1.82  tff(c_201, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_94])).
% 4.51/1.82  tff(c_465, plain, (![A_108, B_109]: (k2_xboole_0(A_108, k4_xboole_0(B_109, A_108))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.82  tff(c_474, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))=k2_xboole_0('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_201, c_465])).
% 4.51/1.82  tff(c_477, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_474])).
% 4.51/1.82  tff(c_580, plain, (![D_117, B_118, A_119]: (~r2_hidden(D_117, B_118) | r2_hidden(D_117, k2_xboole_0(A_119, B_118)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.51/1.82  tff(c_602, plain, (![D_120]: (~r2_hidden(D_120, k1_tarski('#skF_7')) | r2_hidden(D_120, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_580])).
% 4.51/1.82  tff(c_606, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_339, c_602])).
% 4.51/1.82  tff(c_610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_606])).
% 4.51/1.82  tff(c_611, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_94])).
% 4.51/1.82  tff(c_38, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.51/1.82  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/1.82  tff(c_616, plain, (![B_130, A_131]: (k5_xboole_0(B_130, A_131)=k5_xboole_0(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/1.82  tff(c_34, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.51/1.82  tff(c_632, plain, (![A_131]: (k5_xboole_0(k1_xboole_0, A_131)=A_131)), inference(superposition, [status(thm), theory('equality')], [c_616, c_34])).
% 4.51/1.82  tff(c_1237, plain, (![A_178, B_179, C_180]: (k5_xboole_0(k5_xboole_0(A_178, B_179), C_180)=k5_xboole_0(A_178, k5_xboole_0(B_179, C_180)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.51/1.82  tff(c_1301, plain, (![A_24, C_180]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_180))=k5_xboole_0(k1_xboole_0, C_180))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1237])).
% 4.51/1.82  tff(c_1315, plain, (![A_181, C_182]: (k5_xboole_0(A_181, k5_xboole_0(A_181, C_182))=C_182)), inference(demodulation, [status(thm), theory('equality')], [c_632, c_1301])).
% 4.51/1.82  tff(c_1358, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1315])).
% 4.51/1.82  tff(c_761, plain, (![A_140, B_141]: (r1_tarski(k1_tarski(A_140), B_141) | ~r2_hidden(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.82  tff(c_28, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.82  tff(c_765, plain, (![A_140, B_141]: (k2_xboole_0(k1_tarski(A_140), B_141)=B_141 | ~r2_hidden(A_140, B_141))), inference(resolution, [status(thm)], [c_761, c_28])).
% 4.51/1.82  tff(c_1556, plain, (![A_187, B_188]: (k5_xboole_0(k5_xboole_0(A_187, B_188), k2_xboole_0(A_187, B_188))=k3_xboole_0(A_187, B_188))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/1.82  tff(c_1611, plain, (![A_140, B_141]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_140), B_141), B_141)=k3_xboole_0(k1_tarski(A_140), B_141) | ~r2_hidden(A_140, B_141))), inference(superposition, [status(thm), theory('equality')], [c_765, c_1556])).
% 4.51/1.82  tff(c_2320, plain, (![A_232, B_233]: (k3_xboole_0(k1_tarski(A_232), B_233)=k1_tarski(A_232) | ~r2_hidden(A_232, B_233))), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_2, c_1611])).
% 4.51/1.82  tff(c_26, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.82  tff(c_2339, plain, (![A_232, B_233]: (k5_xboole_0(k1_tarski(A_232), k1_tarski(A_232))=k4_xboole_0(k1_tarski(A_232), B_233) | ~r2_hidden(A_232, B_233))), inference(superposition, [status(thm), theory('equality')], [c_2320, c_26])).
% 4.51/1.82  tff(c_2367, plain, (![A_234, B_235]: (k4_xboole_0(k1_tarski(A_234), B_235)=k1_xboole_0 | ~r2_hidden(A_234, B_235))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2339])).
% 4.51/1.82  tff(c_612, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_94])).
% 4.51/1.82  tff(c_92, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.51/1.82  tff(c_712, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_612, c_92])).
% 4.51/1.82  tff(c_2396, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2367, c_712])).
% 4.51/1.82  tff(c_2423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_611, c_2396])).
% 4.51/1.82  tff(c_2424, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 4.51/1.82  tff(c_2426, plain, (![B_236, A_237]: (k5_xboole_0(B_236, A_237)=k5_xboole_0(A_237, B_236))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/1.82  tff(c_2442, plain, (![A_237]: (k5_xboole_0(k1_xboole_0, A_237)=A_237)), inference(superposition, [status(thm), theory('equality')], [c_2426, c_34])).
% 4.51/1.82  tff(c_2928, plain, (![A_289, B_290, C_291]: (k5_xboole_0(k5_xboole_0(A_289, B_290), C_291)=k5_xboole_0(A_289, k5_xboole_0(B_290, C_291)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.51/1.82  tff(c_2992, plain, (![A_24, C_291]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_291))=k5_xboole_0(k1_xboole_0, C_291))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2928])).
% 4.51/1.82  tff(c_3006, plain, (![A_292, C_293]: (k5_xboole_0(A_292, k5_xboole_0(A_292, C_293))=C_293)), inference(demodulation, [status(thm), theory('equality')], [c_2442, c_2992])).
% 4.51/1.82  tff(c_3049, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3006])).
% 4.51/1.82  tff(c_2637, plain, (![A_264, B_265]: (r1_tarski(k1_tarski(A_264), B_265) | ~r2_hidden(A_264, B_265))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.82  tff(c_3655, plain, (![A_317, B_318]: (k2_xboole_0(k1_tarski(A_317), B_318)=B_318 | ~r2_hidden(A_317, B_318))), inference(resolution, [status(thm)], [c_2637, c_28])).
% 4.51/1.82  tff(c_40, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k2_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/1.82  tff(c_3664, plain, (![A_317, B_318]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_317), B_318), B_318)=k3_xboole_0(k1_tarski(A_317), B_318) | ~r2_hidden(A_317, B_318))), inference(superposition, [status(thm), theory('equality')], [c_3655, c_40])).
% 4.51/1.82  tff(c_4178, plain, (![A_359, B_360]: (k3_xboole_0(k1_tarski(A_359), B_360)=k1_tarski(A_359) | ~r2_hidden(A_359, B_360))), inference(demodulation, [status(thm), theory('equality')], [c_3049, c_2, c_3664])).
% 4.51/1.82  tff(c_4197, plain, (![A_359, B_360]: (k5_xboole_0(k1_tarski(A_359), k1_tarski(A_359))=k4_xboole_0(k1_tarski(A_359), B_360) | ~r2_hidden(A_359, B_360))), inference(superposition, [status(thm), theory('equality')], [c_4178, c_26])).
% 4.51/1.82  tff(c_4225, plain, (![A_361, B_362]: (k4_xboole_0(k1_tarski(A_361), B_362)=k1_xboole_0 | ~r2_hidden(A_361, B_362))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4197])).
% 4.51/1.82  tff(c_2425, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 4.51/1.82  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.51/1.82  tff(c_2522, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_88])).
% 4.51/1.82  tff(c_4254, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4225, c_2522])).
% 4.51/1.82  tff(c_4278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2424, c_4254])).
% 4.51/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.82  
% 4.51/1.82  Inference rules
% 4.51/1.82  ----------------------
% 4.51/1.82  #Ref     : 0
% 4.51/1.82  #Sup     : 1005
% 4.51/1.82  #Fact    : 0
% 4.51/1.82  #Define  : 0
% 4.51/1.82  #Split   : 2
% 4.51/1.82  #Chain   : 0
% 4.51/1.82  #Close   : 0
% 4.51/1.82  
% 4.51/1.82  Ordering : KBO
% 4.51/1.82  
% 4.51/1.82  Simplification rules
% 4.51/1.82  ----------------------
% 4.51/1.82  #Subsume      : 72
% 4.51/1.82  #Demod        : 549
% 4.51/1.82  #Tautology    : 706
% 4.51/1.82  #SimpNegUnit  : 2
% 4.51/1.82  #BackRed      : 4
% 4.51/1.82  
% 4.51/1.82  #Partial instantiations: 0
% 4.51/1.82  #Strategies tried      : 1
% 4.51/1.82  
% 4.51/1.82  Timing (in seconds)
% 4.51/1.82  ----------------------
% 4.51/1.82  Preprocessing        : 0.35
% 4.51/1.82  Parsing              : 0.18
% 4.51/1.82  CNF conversion       : 0.03
% 4.51/1.82  Main loop            : 0.70
% 4.51/1.82  Inferencing          : 0.24
% 4.51/1.82  Reduction            : 0.27
% 4.51/1.82  Demodulation         : 0.22
% 4.51/1.82  BG Simplification    : 0.03
% 4.51/1.82  Subsumption          : 0.10
% 4.51/1.82  Abstraction          : 0.05
% 4.51/1.82  MUC search           : 0.00
% 4.51/1.82  Cooper               : 0.00
% 4.51/1.82  Total                : 1.09
% 4.51/1.82  Index Insertion      : 0.00
% 4.51/1.82  Index Deletion       : 0.00
% 4.51/1.82  Index Matching       : 0.00
% 4.51/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
