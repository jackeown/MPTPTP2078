%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:01 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 169 expanded)
%              Number of leaves         :   42 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 185 expanded)
%              Number of equality atoms :   70 ( 124 expanded)
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

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_90,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_192,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_66,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_335,plain,(
    ! [A_92,B_93] : k1_enumset1(A_92,A_92,B_93) = k2_tarski(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    ! [E_33,B_28,C_29] : r2_hidden(E_33,k1_enumset1(E_33,B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_353,plain,(
    ! [A_94,B_95] : r2_hidden(A_94,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_48])).

tff(c_362,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_353])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_194,plain,(
    ! [B_84,A_85] : k5_xboole_0(B_84,A_85) = k5_xboole_0(A_85,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_210,plain,(
    ! [A_85] : k5_xboole_0(k1_xboole_0,A_85) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_32])).

tff(c_36,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_795,plain,(
    ! [A_130,B_131,C_132] : k5_xboole_0(k5_xboole_0(A_130,B_131),C_132) = k5_xboole_0(A_130,k5_xboole_0(B_131,C_132)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_852,plain,(
    ! [A_22,C_132] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_132)) = k5_xboole_0(k1_xboole_0,C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_795])).

tff(c_873,plain,(
    ! [A_133,C_134] : k5_xboole_0(A_133,k5_xboole_0(A_133,C_134)) = C_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_852])).

tff(c_938,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k5_xboole_0(B_136,A_135)) = B_136 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_873])).

tff(c_916,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_873])).

tff(c_941,plain,(
    ! [B_136,A_135] : k5_xboole_0(k5_xboole_0(B_136,A_135),B_136) = A_135 ),
    inference(superposition,[status(thm),theory(equality)],[c_938,c_916])).

tff(c_28,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_94,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_329,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_511,plain,(
    ! [A_108,B_109] : k2_xboole_0(A_108,k4_xboole_0(B_109,A_108)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_528,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = k2_xboole_0('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_511])).

tff(c_533,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_528])).

tff(c_1114,plain,(
    ! [A_139,B_140] : k5_xboole_0(k5_xboole_0(A_139,B_140),k2_xboole_0(A_139,B_140)) = k3_xboole_0(A_139,B_140) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1178,plain,(
    k5_xboole_0(k5_xboole_0('#skF_8',k1_tarski('#skF_7')),'#skF_8') = k3_xboole_0('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_1114])).

tff(c_1226,plain,(
    k3_xboole_0('#skF_8',k1_tarski('#skF_7')) = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1178])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1483,plain,(
    ! [D_152] :
      ( r2_hidden(D_152,'#skF_8')
      | ~ r2_hidden(D_152,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_8])).

tff(c_1487,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_362,c_1483])).

tff(c_1491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_1487])).

tff(c_1492,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_1941,plain,(
    ! [A_193,B_194,C_195] : k5_xboole_0(k5_xboole_0(A_193,B_194),C_195) = k5_xboole_0(A_193,k5_xboole_0(B_194,C_195)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1998,plain,(
    ! [A_22,C_195] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_195)) = k5_xboole_0(k1_xboole_0,C_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1941])).

tff(c_2019,plain,(
    ! [A_196,C_197] : k5_xboole_0(A_196,k5_xboole_0(A_196,C_197)) = C_197 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1998])).

tff(c_2062,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2019])).

tff(c_1495,plain,(
    ! [A_155,B_156] :
      ( r1_tarski(k1_tarski(A_155),B_156)
      | ~ r2_hidden(A_155,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1499,plain,(
    ! [A_155,B_156] :
      ( k2_xboole_0(k1_tarski(A_155),B_156) = B_156
      | ~ r2_hidden(A_155,B_156) ) ),
    inference(resolution,[status(thm)],[c_1495,c_26])).

tff(c_2260,plain,(
    ! [A_202,B_203] : k5_xboole_0(k5_xboole_0(A_202,B_203),k2_xboole_0(A_202,B_203)) = k3_xboole_0(A_202,B_203) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2315,plain,(
    ! [A_155,B_156] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_155),B_156),B_156) = k3_xboole_0(k1_tarski(A_155),B_156)
      | ~ r2_hidden(A_155,B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1499,c_2260])).

tff(c_3091,plain,(
    ! [A_249,B_250] :
      ( k3_xboole_0(k1_tarski(A_249),B_250) = k1_tarski(A_249)
      | ~ r2_hidden(A_249,B_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2062,c_2,c_2315])).

tff(c_24,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3116,plain,(
    ! [A_249,B_250] :
      ( k5_xboole_0(k1_tarski(A_249),k1_tarski(A_249)) = k4_xboole_0(k1_tarski(A_249),B_250)
      | ~ r2_hidden(A_249,B_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3091,c_24])).

tff(c_3147,plain,(
    ! [A_251,B_252] :
      ( k4_xboole_0(k1_tarski(A_251),B_252) = k1_xboole_0
      | ~ r2_hidden(A_251,B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3116])).

tff(c_1493,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_92,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1692,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1493,c_92])).

tff(c_3173,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3147,c_1692])).

tff(c_3202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_3173])).

tff(c_3203,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_3206,plain,(
    ! [B_256,A_257] : k5_xboole_0(B_256,A_257) = k5_xboole_0(A_257,B_256) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3222,plain,(
    ! [A_257] : k5_xboole_0(k1_xboole_0,A_257) = A_257 ),
    inference(superposition,[status(thm),theory(equality)],[c_3206,c_32])).

tff(c_3790,plain,(
    ! [A_302,B_303,C_304] : k5_xboole_0(k5_xboole_0(A_302,B_303),C_304) = k5_xboole_0(A_302,k5_xboole_0(B_303,C_304)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3847,plain,(
    ! [A_22,C_304] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_304)) = k5_xboole_0(k1_xboole_0,C_304) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3790])).

tff(c_3868,plain,(
    ! [A_305,C_306] : k5_xboole_0(A_305,k5_xboole_0(A_305,C_306)) = C_306 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3222,c_3847])).

tff(c_3911,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3868])).

tff(c_82,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3395,plain,(
    ! [A_273,B_274] :
      ( k2_xboole_0(A_273,B_274) = B_274
      | ~ r1_tarski(A_273,B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3399,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(k1_tarski(A_62),B_63) = B_63
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_82,c_3395])).

tff(c_4109,plain,(
    ! [A_311,B_312] : k5_xboole_0(k5_xboole_0(A_311,B_312),k2_xboole_0(A_311,B_312)) = k3_xboole_0(A_311,B_312) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4164,plain,(
    ! [A_62,B_63] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_62),B_63),B_63) = k3_xboole_0(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_4109])).

tff(c_4956,plain,(
    ! [A_361,B_362] :
      ( k3_xboole_0(k1_tarski(A_361),B_362) = k1_tarski(A_361)
      | ~ r2_hidden(A_361,B_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3911,c_2,c_4164])).

tff(c_4984,plain,(
    ! [A_361,B_362] :
      ( k5_xboole_0(k1_tarski(A_361),k1_tarski(A_361)) = k4_xboole_0(k1_tarski(A_361),B_362)
      | ~ r2_hidden(A_361,B_362) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4956,c_24])).

tff(c_5021,plain,(
    ! [A_370,B_371] :
      ( k4_xboole_0(k1_tarski(A_370),B_371) = k1_xboole_0
      | ~ r2_hidden(A_370,B_371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4984])).

tff(c_3204,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3378,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3204,c_88])).

tff(c_5050,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5021,c_3378])).

tff(c_5074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3203,c_5050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/2.06  
% 5.05/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/2.06  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 5.05/2.06  
% 5.05/2.06  %Foreground sorts:
% 5.05/2.06  
% 5.05/2.06  
% 5.05/2.06  %Background operators:
% 5.05/2.06  
% 5.05/2.06  
% 5.05/2.06  %Foreground operators:
% 5.05/2.06  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.05/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.05/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.05/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.05/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.05/2.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.05/2.06  tff('#skF_7', type, '#skF_7': $i).
% 5.05/2.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.05/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/2.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.05/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.05/2.06  tff('#skF_5', type, '#skF_5': $i).
% 5.05/2.06  tff('#skF_6', type, '#skF_6': $i).
% 5.05/2.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.05/2.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.05/2.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.05/2.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.05/2.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.05/2.06  tff('#skF_8', type, '#skF_8': $i).
% 5.05/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.05/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.05/2.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.05/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.05/2.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.05/2.06  
% 5.05/2.08  tff(f_100, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 5.05/2.08  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.05/2.08  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.05/2.08  tff(f_73, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.05/2.08  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.05/2.08  tff(f_50, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.05/2.08  tff(f_54, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.05/2.08  tff(f_52, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.05/2.08  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.05/2.08  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.05/2.08  tff(f_56, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.05/2.08  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.05/2.08  tff(f_91, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.05/2.08  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.05/2.08  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.05/2.08  tff(c_90, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.05/2.08  tff(c_192, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 5.05/2.08  tff(c_66, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.05/2.08  tff(c_335, plain, (![A_92, B_93]: (k1_enumset1(A_92, A_92, B_93)=k2_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.05/2.08  tff(c_48, plain, (![E_33, B_28, C_29]: (r2_hidden(E_33, k1_enumset1(E_33, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.05/2.08  tff(c_353, plain, (![A_94, B_95]: (r2_hidden(A_94, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_335, c_48])).
% 5.05/2.08  tff(c_362, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_353])).
% 5.05/2.08  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.05/2.08  tff(c_194, plain, (![B_84, A_85]: (k5_xboole_0(B_84, A_85)=k5_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.05/2.08  tff(c_32, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.05/2.08  tff(c_210, plain, (![A_85]: (k5_xboole_0(k1_xboole_0, A_85)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_194, c_32])).
% 5.05/2.08  tff(c_36, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.05/2.08  tff(c_795, plain, (![A_130, B_131, C_132]: (k5_xboole_0(k5_xboole_0(A_130, B_131), C_132)=k5_xboole_0(A_130, k5_xboole_0(B_131, C_132)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.05/2.08  tff(c_852, plain, (![A_22, C_132]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_132))=k5_xboole_0(k1_xboole_0, C_132))), inference(superposition, [status(thm), theory('equality')], [c_36, c_795])).
% 5.05/2.08  tff(c_873, plain, (![A_133, C_134]: (k5_xboole_0(A_133, k5_xboole_0(A_133, C_134))=C_134)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_852])).
% 5.05/2.08  tff(c_938, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k5_xboole_0(B_136, A_135))=B_136)), inference(superposition, [status(thm), theory('equality')], [c_2, c_873])).
% 5.05/2.08  tff(c_916, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_873])).
% 5.05/2.08  tff(c_941, plain, (![B_136, A_135]: (k5_xboole_0(k5_xboole_0(B_136, A_135), B_136)=A_135)), inference(superposition, [status(thm), theory('equality')], [c_938, c_916])).
% 5.05/2.08  tff(c_28, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.05/2.08  tff(c_94, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.05/2.08  tff(c_329, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_94])).
% 5.05/2.08  tff(c_511, plain, (![A_108, B_109]: (k2_xboole_0(A_108, k4_xboole_0(B_109, A_108))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.05/2.08  tff(c_528, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))=k2_xboole_0('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_329, c_511])).
% 5.05/2.08  tff(c_533, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_528])).
% 5.05/2.08  tff(c_1114, plain, (![A_139, B_140]: (k5_xboole_0(k5_xboole_0(A_139, B_140), k2_xboole_0(A_139, B_140))=k3_xboole_0(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.05/2.08  tff(c_1178, plain, (k5_xboole_0(k5_xboole_0('#skF_8', k1_tarski('#skF_7')), '#skF_8')=k3_xboole_0('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_1114])).
% 5.05/2.08  tff(c_1226, plain, (k3_xboole_0('#skF_8', k1_tarski('#skF_7'))=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_941, c_1178])).
% 5.05/2.08  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.05/2.08  tff(c_1483, plain, (![D_152]: (r2_hidden(D_152, '#skF_8') | ~r2_hidden(D_152, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1226, c_8])).
% 5.05/2.08  tff(c_1487, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_362, c_1483])).
% 5.05/2.08  tff(c_1491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_1487])).
% 5.05/2.08  tff(c_1492, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_94])).
% 5.05/2.08  tff(c_1941, plain, (![A_193, B_194, C_195]: (k5_xboole_0(k5_xboole_0(A_193, B_194), C_195)=k5_xboole_0(A_193, k5_xboole_0(B_194, C_195)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.05/2.08  tff(c_1998, plain, (![A_22, C_195]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_195))=k5_xboole_0(k1_xboole_0, C_195))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1941])).
% 5.05/2.08  tff(c_2019, plain, (![A_196, C_197]: (k5_xboole_0(A_196, k5_xboole_0(A_196, C_197))=C_197)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1998])).
% 5.05/2.08  tff(c_2062, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2019])).
% 5.05/2.08  tff(c_1495, plain, (![A_155, B_156]: (r1_tarski(k1_tarski(A_155), B_156) | ~r2_hidden(A_155, B_156))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.05/2.08  tff(c_26, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.05/2.08  tff(c_1499, plain, (![A_155, B_156]: (k2_xboole_0(k1_tarski(A_155), B_156)=B_156 | ~r2_hidden(A_155, B_156))), inference(resolution, [status(thm)], [c_1495, c_26])).
% 5.05/2.08  tff(c_2260, plain, (![A_202, B_203]: (k5_xboole_0(k5_xboole_0(A_202, B_203), k2_xboole_0(A_202, B_203))=k3_xboole_0(A_202, B_203))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.05/2.08  tff(c_2315, plain, (![A_155, B_156]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_155), B_156), B_156)=k3_xboole_0(k1_tarski(A_155), B_156) | ~r2_hidden(A_155, B_156))), inference(superposition, [status(thm), theory('equality')], [c_1499, c_2260])).
% 5.05/2.08  tff(c_3091, plain, (![A_249, B_250]: (k3_xboole_0(k1_tarski(A_249), B_250)=k1_tarski(A_249) | ~r2_hidden(A_249, B_250))), inference(demodulation, [status(thm), theory('equality')], [c_2062, c_2, c_2315])).
% 5.05/2.08  tff(c_24, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.05/2.08  tff(c_3116, plain, (![A_249, B_250]: (k5_xboole_0(k1_tarski(A_249), k1_tarski(A_249))=k4_xboole_0(k1_tarski(A_249), B_250) | ~r2_hidden(A_249, B_250))), inference(superposition, [status(thm), theory('equality')], [c_3091, c_24])).
% 5.05/2.08  tff(c_3147, plain, (![A_251, B_252]: (k4_xboole_0(k1_tarski(A_251), B_252)=k1_xboole_0 | ~r2_hidden(A_251, B_252))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3116])).
% 5.05/2.08  tff(c_1493, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_94])).
% 5.05/2.08  tff(c_92, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.05/2.08  tff(c_1692, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1493, c_92])).
% 5.05/2.08  tff(c_3173, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3147, c_1692])).
% 5.05/2.08  tff(c_3202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1492, c_3173])).
% 5.05/2.08  tff(c_3203, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 5.05/2.08  tff(c_3206, plain, (![B_256, A_257]: (k5_xboole_0(B_256, A_257)=k5_xboole_0(A_257, B_256))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.05/2.08  tff(c_3222, plain, (![A_257]: (k5_xboole_0(k1_xboole_0, A_257)=A_257)), inference(superposition, [status(thm), theory('equality')], [c_3206, c_32])).
% 5.05/2.08  tff(c_3790, plain, (![A_302, B_303, C_304]: (k5_xboole_0(k5_xboole_0(A_302, B_303), C_304)=k5_xboole_0(A_302, k5_xboole_0(B_303, C_304)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.05/2.08  tff(c_3847, plain, (![A_22, C_304]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_304))=k5_xboole_0(k1_xboole_0, C_304))), inference(superposition, [status(thm), theory('equality')], [c_36, c_3790])).
% 5.05/2.08  tff(c_3868, plain, (![A_305, C_306]: (k5_xboole_0(A_305, k5_xboole_0(A_305, C_306))=C_306)), inference(demodulation, [status(thm), theory('equality')], [c_3222, c_3847])).
% 5.05/2.08  tff(c_3911, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3868])).
% 5.05/2.08  tff(c_82, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.05/2.08  tff(c_3395, plain, (![A_273, B_274]: (k2_xboole_0(A_273, B_274)=B_274 | ~r1_tarski(A_273, B_274))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.05/2.08  tff(c_3399, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), B_63)=B_63 | ~r2_hidden(A_62, B_63))), inference(resolution, [status(thm)], [c_82, c_3395])).
% 5.05/2.08  tff(c_4109, plain, (![A_311, B_312]: (k5_xboole_0(k5_xboole_0(A_311, B_312), k2_xboole_0(A_311, B_312))=k3_xboole_0(A_311, B_312))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.05/2.08  tff(c_4164, plain, (![A_62, B_63]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_62), B_63), B_63)=k3_xboole_0(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_3399, c_4109])).
% 5.05/2.08  tff(c_4956, plain, (![A_361, B_362]: (k3_xboole_0(k1_tarski(A_361), B_362)=k1_tarski(A_361) | ~r2_hidden(A_361, B_362))), inference(demodulation, [status(thm), theory('equality')], [c_3911, c_2, c_4164])).
% 5.05/2.08  tff(c_4984, plain, (![A_361, B_362]: (k5_xboole_0(k1_tarski(A_361), k1_tarski(A_361))=k4_xboole_0(k1_tarski(A_361), B_362) | ~r2_hidden(A_361, B_362))), inference(superposition, [status(thm), theory('equality')], [c_4956, c_24])).
% 5.05/2.08  tff(c_5021, plain, (![A_370, B_371]: (k4_xboole_0(k1_tarski(A_370), B_371)=k1_xboole_0 | ~r2_hidden(A_370, B_371))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4984])).
% 5.05/2.08  tff(c_3204, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 5.05/2.08  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.05/2.08  tff(c_3378, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3204, c_88])).
% 5.05/2.08  tff(c_5050, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5021, c_3378])).
% 5.05/2.08  tff(c_5074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3203, c_5050])).
% 5.05/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/2.08  
% 5.05/2.08  Inference rules
% 5.05/2.08  ----------------------
% 5.05/2.08  #Ref     : 0
% 5.05/2.08  #Sup     : 1184
% 5.05/2.08  #Fact    : 0
% 5.05/2.08  #Define  : 0
% 5.05/2.08  #Split   : 2
% 5.05/2.08  #Chain   : 0
% 5.05/2.08  #Close   : 0
% 5.05/2.08  
% 5.05/2.08  Ordering : KBO
% 5.05/2.08  
% 5.05/2.08  Simplification rules
% 5.05/2.08  ----------------------
% 5.05/2.08  #Subsume      : 72
% 5.05/2.08  #Demod        : 665
% 5.05/2.08  #Tautology    : 801
% 5.05/2.08  #SimpNegUnit  : 2
% 5.05/2.08  #BackRed      : 6
% 5.05/2.08  
% 5.05/2.08  #Partial instantiations: 0
% 5.05/2.08  #Strategies tried      : 1
% 5.05/2.08  
% 5.05/2.08  Timing (in seconds)
% 5.05/2.08  ----------------------
% 5.05/2.09  Preprocessing        : 0.47
% 5.05/2.09  Parsing              : 0.18
% 5.05/2.09  CNF conversion       : 0.06
% 5.05/2.09  Main loop            : 0.80
% 5.05/2.09  Inferencing          : 0.27
% 5.05/2.09  Reduction            : 0.32
% 5.05/2.09  Demodulation         : 0.26
% 5.05/2.09  BG Simplification    : 0.05
% 5.05/2.09  Subsumption          : 0.11
% 5.05/2.09  Abstraction          : 0.05
% 5.05/2.09  MUC search           : 0.00
% 5.05/2.09  Cooper               : 0.00
% 5.05/2.09  Total                : 1.32
% 5.05/2.09  Index Insertion      : 0.00
% 5.05/2.09  Index Deletion       : 0.00
% 5.05/2.09  Index Matching       : 0.00
% 5.05/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
