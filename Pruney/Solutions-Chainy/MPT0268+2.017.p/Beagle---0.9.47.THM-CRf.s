%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:36 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 169 expanded)
%              Number of leaves         :   39 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 244 expanded)
%              Number of equality atoms :   40 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_76,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_136,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_30,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(k1_tarski(A_56),B_57)
      | r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_168,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_180,plain,(
    ! [A_86,B_87] :
      ( ~ r1_xboole_0(A_86,B_87)
      | k3_xboole_0(A_86,B_87) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_168])).

tff(c_1073,plain,(
    ! [A_168,B_169] :
      ( k3_xboole_0(k1_tarski(A_168),B_169) = k1_xboole_0
      | r2_hidden(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_72,c_180])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_234,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_249,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_234])).

tff(c_1101,plain,(
    ! [B_169,A_168] :
      ( k4_xboole_0(B_169,k1_tarski(A_168)) = k5_xboole_0(B_169,k1_xboole_0)
      | r2_hidden(A_168,B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_249])).

tff(c_1162,plain,(
    ! [B_170,A_171] :
      ( k4_xboole_0(B_170,k1_tarski(A_171)) = B_170
      | r2_hidden(A_171,B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1101])).

tff(c_74,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_189,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_1184,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_189])).

tff(c_1201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1184])).

tff(c_1202,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_58,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_138,plain,(
    ! [A_74,B_75] : k1_enumset1(A_74,A_74,B_75) = k2_tarski(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [E_27,A_21,B_22] : r2_hidden(E_27,k1_enumset1(A_21,B_22,E_27)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_156,plain,(
    ! [B_76,A_77] : r2_hidden(B_76,k2_tarski(A_77,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_36])).

tff(c_159,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_156])).

tff(c_1203,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_32,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1207,plain,(
    r1_xboole_0('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_32])).

tff(c_179,plain,(
    ! [A_83,B_84] :
      ( ~ r1_xboole_0(A_83,B_84)
      | k3_xboole_0(A_83,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_168])).

tff(c_1214,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1207,c_179])).

tff(c_24,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1218,plain,(
    ! [C_13] :
      ( ~ r1_xboole_0('#skF_7',k1_tarski('#skF_8'))
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_24])).

tff(c_1222,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_1218])).

tff(c_78,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1225,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_78])).

tff(c_1229,plain,(
    r1_xboole_0('#skF_9',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_32])).

tff(c_1243,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1229,c_179])).

tff(c_2149,plain,(
    ! [D_219,A_220,B_221] :
      ( r2_hidden(D_219,k3_xboole_0(A_220,B_221))
      | ~ r2_hidden(D_219,B_221)
      | ~ r2_hidden(D_219,A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2185,plain,(
    ! [D_219] :
      ( r2_hidden(D_219,k1_xboole_0)
      | ~ r2_hidden(D_219,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_219,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1243,c_2149])).

tff(c_2228,plain,(
    ! [D_223] :
      ( ~ r2_hidden(D_223,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_223,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1222,c_2185])).

tff(c_2236,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_159,c_2228])).

tff(c_2245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_2236])).

tff(c_2246,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2249,plain,(
    ! [A_227,B_228] : k1_enumset1(A_227,A_227,B_228) = k2_tarski(A_227,B_228) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2267,plain,(
    ! [B_229,A_230] : r2_hidden(B_229,k2_tarski(A_230,B_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2249,c_36])).

tff(c_2270,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2267])).

tff(c_2247,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2293,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2247,c_80])).

tff(c_2297,plain,(
    r1_xboole_0('#skF_9',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2293,c_32])).

tff(c_2301,plain,(
    ! [A_239,B_240,C_241] :
      ( ~ r1_xboole_0(A_239,B_240)
      | ~ r2_hidden(C_241,k3_xboole_0(A_239,B_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2313,plain,(
    ! [A_242,B_243] :
      ( ~ r1_xboole_0(A_242,B_243)
      | k3_xboole_0(A_242,B_243) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_2301])).

tff(c_2323,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2297,c_2313])).

tff(c_2329,plain,(
    ! [C_13] :
      ( ~ r1_xboole_0('#skF_9',k1_tarski('#skF_10'))
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2323,c_24])).

tff(c_2336,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2297,c_2329])).

tff(c_2346,plain,(
    ! [A_245,B_246] : k3_xboole_0(k4_xboole_0(A_245,B_246),B_246) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_2313])).

tff(c_2379,plain,(
    ! [B_247,A_248] : k3_xboole_0(B_247,k4_xboole_0(A_248,B_247)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2346,c_2])).

tff(c_2392,plain,(
    k3_xboole_0(k1_tarski('#skF_10'),'#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2293,c_2379])).

tff(c_2762,plain,(
    ! [D_276,A_277,B_278] :
      ( r2_hidden(D_276,k3_xboole_0(A_277,B_278))
      | ~ r2_hidden(D_276,B_278)
      | ~ r2_hidden(D_276,A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2777,plain,(
    ! [D_276] :
      ( r2_hidden(D_276,k1_xboole_0)
      | ~ r2_hidden(D_276,'#skF_9')
      | ~ r2_hidden(D_276,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2392,c_2762])).

tff(c_2889,plain,(
    ! [D_282] :
      ( ~ r2_hidden(D_282,'#skF_9')
      | ~ r2_hidden(D_282,k1_tarski('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2336,c_2777])).

tff(c_2897,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_2270,c_2889])).

tff(c_2906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_2897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.75  
% 3.83/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.76  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5
% 3.83/1.76  
% 3.83/1.76  %Foreground sorts:
% 3.83/1.76  
% 3.83/1.76  
% 3.83/1.76  %Background operators:
% 3.83/1.76  
% 3.83/1.76  
% 3.83/1.76  %Foreground operators:
% 3.83/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.83/1.76  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.83/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.83/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.83/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.83/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.83/1.76  tff('#skF_7', type, '#skF_7': $i).
% 3.83/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.83/1.76  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.83/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.83/1.76  tff('#skF_10', type, '#skF_10': $i).
% 3.83/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.83/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.83/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.83/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.83/1.76  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.83/1.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.76  tff('#skF_9', type, '#skF_9': $i).
% 3.83/1.76  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.76  tff('#skF_8', type, '#skF_8': $i).
% 3.83/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.76  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.83/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.76  
% 3.83/1.77  tff(f_104, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.83/1.77  tff(f_62, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.83/1.77  tff(f_98, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.83/1.77  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.83/1.77  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.83/1.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.83/1.77  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.83/1.77  tff(f_81, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.83/1.77  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.83/1.77  tff(f_79, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.83/1.77  tff(f_64, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.83/1.77  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.83/1.77  tff(c_76, plain, (~r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.83/1.77  tff(c_136, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_76])).
% 3.83/1.77  tff(c_30, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.83/1.77  tff(c_72, plain, (![A_56, B_57]: (r1_xboole_0(k1_tarski(A_56), B_57) | r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.83/1.77  tff(c_26, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.77  tff(c_168, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.83/1.77  tff(c_180, plain, (![A_86, B_87]: (~r1_xboole_0(A_86, B_87) | k3_xboole_0(A_86, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_168])).
% 3.83/1.77  tff(c_1073, plain, (![A_168, B_169]: (k3_xboole_0(k1_tarski(A_168), B_169)=k1_xboole_0 | r2_hidden(A_168, B_169))), inference(resolution, [status(thm)], [c_72, c_180])).
% 3.83/1.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.83/1.77  tff(c_234, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.83/1.77  tff(c_249, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_234])).
% 3.83/1.77  tff(c_1101, plain, (![B_169, A_168]: (k4_xboole_0(B_169, k1_tarski(A_168))=k5_xboole_0(B_169, k1_xboole_0) | r2_hidden(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_249])).
% 3.83/1.77  tff(c_1162, plain, (![B_170, A_171]: (k4_xboole_0(B_170, k1_tarski(A_171))=B_170 | r2_hidden(A_171, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1101])).
% 3.83/1.77  tff(c_74, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.83/1.77  tff(c_189, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 3.83/1.77  tff(c_1184, plain, (r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1162, c_189])).
% 3.83/1.77  tff(c_1201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_1184])).
% 3.83/1.77  tff(c_1202, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_74])).
% 3.83/1.77  tff(c_58, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.83/1.77  tff(c_138, plain, (![A_74, B_75]: (k1_enumset1(A_74, A_74, B_75)=k2_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.83/1.77  tff(c_36, plain, (![E_27, A_21, B_22]: (r2_hidden(E_27, k1_enumset1(A_21, B_22, E_27)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.83/1.77  tff(c_156, plain, (![B_76, A_77]: (r2_hidden(B_76, k2_tarski(A_77, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_36])).
% 3.83/1.77  tff(c_159, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_156])).
% 3.83/1.77  tff(c_1203, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 3.83/1.77  tff(c_32, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.83/1.77  tff(c_1207, plain, (r1_xboole_0('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1203, c_32])).
% 3.83/1.77  tff(c_179, plain, (![A_83, B_84]: (~r1_xboole_0(A_83, B_84) | k3_xboole_0(A_83, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_168])).
% 3.83/1.77  tff(c_1214, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1207, c_179])).
% 3.83/1.77  tff(c_24, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.83/1.77  tff(c_1218, plain, (![C_13]: (~r1_xboole_0('#skF_7', k1_tarski('#skF_8')) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1214, c_24])).
% 3.83/1.77  tff(c_1222, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_1218])).
% 3.83/1.77  tff(c_78, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.83/1.77  tff(c_1225, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1203, c_78])).
% 3.83/1.77  tff(c_1229, plain, (r1_xboole_0('#skF_9', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1225, c_32])).
% 3.83/1.77  tff(c_1243, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1229, c_179])).
% 3.83/1.77  tff(c_2149, plain, (![D_219, A_220, B_221]: (r2_hidden(D_219, k3_xboole_0(A_220, B_221)) | ~r2_hidden(D_219, B_221) | ~r2_hidden(D_219, A_220))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.83/1.77  tff(c_2185, plain, (![D_219]: (r2_hidden(D_219, k1_xboole_0) | ~r2_hidden(D_219, k1_tarski('#skF_10')) | ~r2_hidden(D_219, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1243, c_2149])).
% 3.83/1.77  tff(c_2228, plain, (![D_223]: (~r2_hidden(D_223, k1_tarski('#skF_10')) | ~r2_hidden(D_223, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1222, c_2185])).
% 3.83/1.77  tff(c_2236, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_159, c_2228])).
% 3.83/1.77  tff(c_2245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1202, c_2236])).
% 3.83/1.77  tff(c_2246, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_76])).
% 3.83/1.77  tff(c_2249, plain, (![A_227, B_228]: (k1_enumset1(A_227, A_227, B_228)=k2_tarski(A_227, B_228))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.83/1.77  tff(c_2267, plain, (![B_229, A_230]: (r2_hidden(B_229, k2_tarski(A_230, B_229)))), inference(superposition, [status(thm), theory('equality')], [c_2249, c_36])).
% 3.83/1.77  tff(c_2270, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2267])).
% 3.83/1.77  tff(c_2247, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 3.83/1.77  tff(c_80, plain, (~r2_hidden('#skF_8', '#skF_7') | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.83/1.77  tff(c_2293, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2247, c_80])).
% 3.83/1.77  tff(c_2297, plain, (r1_xboole_0('#skF_9', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2293, c_32])).
% 3.83/1.77  tff(c_2301, plain, (![A_239, B_240, C_241]: (~r1_xboole_0(A_239, B_240) | ~r2_hidden(C_241, k3_xboole_0(A_239, B_240)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.83/1.77  tff(c_2313, plain, (![A_242, B_243]: (~r1_xboole_0(A_242, B_243) | k3_xboole_0(A_242, B_243)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_2301])).
% 3.83/1.77  tff(c_2323, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2297, c_2313])).
% 3.83/1.77  tff(c_2329, plain, (![C_13]: (~r1_xboole_0('#skF_9', k1_tarski('#skF_10')) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2323, c_24])).
% 3.83/1.77  tff(c_2336, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2297, c_2329])).
% 3.83/1.77  tff(c_2346, plain, (![A_245, B_246]: (k3_xboole_0(k4_xboole_0(A_245, B_246), B_246)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_2313])).
% 3.83/1.77  tff(c_2379, plain, (![B_247, A_248]: (k3_xboole_0(B_247, k4_xboole_0(A_248, B_247))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2346, c_2])).
% 3.83/1.77  tff(c_2392, plain, (k3_xboole_0(k1_tarski('#skF_10'), '#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2293, c_2379])).
% 3.83/1.77  tff(c_2762, plain, (![D_276, A_277, B_278]: (r2_hidden(D_276, k3_xboole_0(A_277, B_278)) | ~r2_hidden(D_276, B_278) | ~r2_hidden(D_276, A_277))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.83/1.77  tff(c_2777, plain, (![D_276]: (r2_hidden(D_276, k1_xboole_0) | ~r2_hidden(D_276, '#skF_9') | ~r2_hidden(D_276, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_2392, c_2762])).
% 3.83/1.77  tff(c_2889, plain, (![D_282]: (~r2_hidden(D_282, '#skF_9') | ~r2_hidden(D_282, k1_tarski('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_2336, c_2777])).
% 3.83/1.77  tff(c_2897, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_2270, c_2889])).
% 3.83/1.77  tff(c_2906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2246, c_2897])).
% 3.83/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.77  
% 3.83/1.77  Inference rules
% 3.83/1.77  ----------------------
% 3.83/1.77  #Ref     : 0
% 3.83/1.77  #Sup     : 679
% 3.83/1.77  #Fact    : 0
% 3.83/1.77  #Define  : 0
% 3.83/1.77  #Split   : 2
% 3.83/1.77  #Chain   : 0
% 3.83/1.77  #Close   : 0
% 3.83/1.77  
% 3.83/1.77  Ordering : KBO
% 3.83/1.77  
% 3.83/1.77  Simplification rules
% 3.83/1.77  ----------------------
% 3.83/1.77  #Subsume      : 123
% 3.83/1.77  #Demod        : 282
% 3.83/1.77  #Tautology    : 356
% 3.83/1.77  #SimpNegUnit  : 51
% 3.83/1.77  #BackRed      : 0
% 3.83/1.77  
% 3.83/1.77  #Partial instantiations: 0
% 3.83/1.77  #Strategies tried      : 1
% 3.83/1.77  
% 3.83/1.77  Timing (in seconds)
% 3.83/1.77  ----------------------
% 3.83/1.78  Preprocessing        : 0.37
% 3.83/1.78  Parsing              : 0.19
% 3.83/1.78  CNF conversion       : 0.03
% 3.83/1.78  Main loop            : 0.56
% 3.83/1.78  Inferencing          : 0.20
% 3.83/1.78  Reduction            : 0.20
% 3.83/1.78  Demodulation         : 0.15
% 3.83/1.78  BG Simplification    : 0.03
% 3.83/1.78  Subsumption          : 0.09
% 3.83/1.78  Abstraction          : 0.03
% 3.83/1.78  MUC search           : 0.00
% 3.83/1.78  Cooper               : 0.00
% 3.83/1.78  Total                : 0.97
% 3.83/1.78  Index Insertion      : 0.00
% 3.83/1.78  Index Deletion       : 0.00
% 3.83/1.78  Index Matching       : 0.00
% 3.83/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
