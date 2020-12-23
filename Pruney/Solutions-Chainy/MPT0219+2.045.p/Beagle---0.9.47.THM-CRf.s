%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:55 EST 2020

% Result     : Theorem 5.27s
% Output     : CNFRefutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 604 expanded)
%              Number of leaves         :   32 ( 217 expanded)
%              Depth                    :   18
%              Number of atoms          :   96 ( 999 expanded)
%              Number of equality atoms :   57 ( 377 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_60,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_428,plain,(
    ! [D_75,A_76,B_77] :
      ( r2_hidden(D_75,A_76)
      | ~ r2_hidden(D_75,k4_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_439,plain,(
    ! [A_76,B_77,B_4] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_76,B_77),B_4),A_76)
      | r1_tarski(k4_xboole_0(A_76,B_77),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_428])).

tff(c_440,plain,(
    ! [D_78,B_79,A_80] :
      ( ~ r2_hidden(D_78,B_79)
      | ~ r2_hidden(D_78,k4_xboole_0(A_80,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2057,plain,(
    ! [A_177,B_178,B_179] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_177,B_178),B_179),B_178)
      | r1_tarski(k4_xboole_0(A_177,B_178),B_179) ) ),
    inference(resolution,[status(thm)],[c_8,c_440])).

tff(c_2089,plain,(
    ! [A_180,B_181] : r1_tarski(k4_xboole_0(A_180,A_180),B_181) ),
    inference(resolution,[status(thm)],[c_439,c_2057])).

tff(c_38,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_452,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_460,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_452])).

tff(c_2116,plain,(
    ! [A_180] : k4_xboole_0(A_180,A_180) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2089,c_460])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_130,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_118])).

tff(c_273,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_288,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_273])).

tff(c_2128,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_288])).

tff(c_131,plain,(
    ! [A_53] : k3_xboole_0(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_118])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [A_53] : k3_xboole_0(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_2])).

tff(c_285,plain,(
    ! [A_53] : k5_xboole_0(A_53,k1_xboole_0) = k4_xboole_0(A_53,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_273])).

tff(c_300,plain,(
    ! [A_53] : k4_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_285])).

tff(c_645,plain,(
    ! [A_104,B_105,C_106] : k5_xboole_0(k5_xboole_0(A_104,B_105),C_106) = k5_xboole_0(A_104,k5_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2484,plain,(
    ! [A_191,B_192,B_193] : k5_xboole_0(A_191,k5_xboole_0(B_192,k4_xboole_0(B_193,k5_xboole_0(A_191,B_192)))) = k2_xboole_0(k5_xboole_0(A_191,B_192),B_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_48])).

tff(c_2533,plain,(
    ! [B_15,B_193] : k5_xboole_0(B_15,k5_xboole_0(B_15,k4_xboole_0(B_193,k1_xboole_0))) = k2_xboole_0(k5_xboole_0(B_15,B_15),B_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_2484])).

tff(c_2879,plain,(
    ! [B_198,B_199] : k5_xboole_0(B_198,k5_xboole_0(B_198,B_199)) = k2_xboole_0(k1_xboole_0,B_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_300,c_2533])).

tff(c_2952,plain,(
    ! [B_15] : k5_xboole_0(B_15,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_2879])).

tff(c_3019,plain,(
    ! [B_15] : k2_xboole_0(k1_xboole_0,B_15) = B_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2952])).

tff(c_313,plain,(
    ! [A_67] : k4_xboole_0(A_67,k1_xboole_0) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_285])).

tff(c_323,plain,(
    ! [A_67] : k5_xboole_0(k1_xboole_0,A_67) = k2_xboole_0(k1_xboole_0,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_48])).

tff(c_3030,plain,(
    ! [A_67] : k5_xboole_0(k1_xboole_0,A_67) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3019,c_323])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2625,plain,(
    ! [B_15,B_193] : k5_xboole_0(B_15,k5_xboole_0(B_15,B_193)) = k2_xboole_0(k1_xboole_0,B_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_300,c_2533])).

tff(c_3227,plain,(
    ! [B_202,B_203] : k5_xboole_0(B_202,k5_xboole_0(B_202,B_203)) = B_203 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3019,c_2625])).

tff(c_3891,plain,(
    ! [A_213,B_214] : k5_xboole_0(A_213,k2_xboole_0(A_213,B_214)) = k4_xboole_0(B_214,A_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_3227])).

tff(c_3960,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_3891])).

tff(c_3973,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_3960])).

tff(c_2206,plain,(
    ! [B_183] : k5_xboole_0(B_183,B_183) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_288])).

tff(c_34,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_697,plain,(
    ! [A_16,B_17,C_106] : k5_xboole_0(A_16,k5_xboole_0(k3_xboole_0(A_16,B_17),C_106)) = k5_xboole_0(k4_xboole_0(A_16,B_17),C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_645])).

tff(c_2212,plain,(
    ! [A_16,B_17] : k5_xboole_0(k4_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k5_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2206,c_697])).

tff(c_4310,plain,(
    ! [A_222,B_223] : k5_xboole_0(k4_xboole_0(A_222,B_223),k3_xboole_0(A_222,B_223)) = A_222 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2212])).

tff(c_4349,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_4'))) = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3973,c_4310])).

tff(c_4397,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3030,c_2,c_4349])).

tff(c_3325,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3227])).

tff(c_1342,plain,(
    ! [A_140,B_141,B_142] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_140,B_141),B_142),A_140)
      | r1_tarski(k4_xboole_0(A_140,B_141),B_142) ) ),
    inference(resolution,[status(thm)],[c_8,c_428])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1388,plain,(
    ! [A_143,B_144] : r1_tarski(k4_xboole_0(A_143,B_144),A_143) ),
    inference(resolution,[status(thm)],[c_1342,c_6])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1465,plain,(
    ! [A_148,B_149] : k3_xboole_0(k4_xboole_0(A_148,B_149),A_148) = k4_xboole_0(A_148,B_149) ),
    inference(resolution,[status(thm)],[c_1388,c_36])).

tff(c_297,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_273])).

tff(c_1474,plain,(
    ! [A_148,B_149] : k5_xboole_0(A_148,k4_xboole_0(A_148,B_149)) = k4_xboole_0(A_148,k4_xboole_0(A_148,B_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1465,c_297])).

tff(c_5557,plain,(
    ! [A_251,B_252] : k4_xboole_0(A_251,k4_xboole_0(A_251,B_252)) = k3_xboole_0(A_251,B_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3325,c_1474])).

tff(c_1384,plain,(
    ! [A_140,B_141] : r1_tarski(k4_xboole_0(A_140,B_141),A_140) ),
    inference(resolution,[status(thm)],[c_1342,c_6])).

tff(c_5701,plain,(
    ! [A_255,B_256] : r1_tarski(k3_xboole_0(A_255,B_256),A_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_5557,c_1384])).

tff(c_5722,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4397,c_5701])).

tff(c_58,plain,(
    ! [B_42,A_41] :
      ( B_42 = A_41
      | ~ r1_tarski(k1_tarski(A_41),k1_tarski(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5828,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5722,c_58])).

tff(c_5836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.27/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/2.08  
% 5.27/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/2.08  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.27/2.08  
% 5.27/2.08  %Foreground sorts:
% 5.27/2.08  
% 5.27/2.08  
% 5.27/2.08  %Background operators:
% 5.27/2.08  
% 5.27/2.08  
% 5.27/2.08  %Foreground operators:
% 5.27/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.27/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.27/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.27/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.27/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.27/2.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.27/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.27/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.27/2.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.27/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.27/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.27/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.27/2.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.27/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.27/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.27/2.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.27/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.27/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.27/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.27/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.27/2.08  
% 5.39/2.10  tff(f_85, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 5.39/2.10  tff(f_62, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.39/2.10  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.39/2.10  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.39/2.10  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.39/2.10  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.39/2.10  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.39/2.10  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.39/2.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.39/2.10  tff(f_66, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.39/2.10  tff(f_68, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.39/2.10  tff(f_80, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 5.39/2.10  tff(c_60, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.39/2.10  tff(c_42, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.39/2.10  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.39/2.10  tff(c_428, plain, (![D_75, A_76, B_77]: (r2_hidden(D_75, A_76) | ~r2_hidden(D_75, k4_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.39/2.10  tff(c_439, plain, (![A_76, B_77, B_4]: (r2_hidden('#skF_1'(k4_xboole_0(A_76, B_77), B_4), A_76) | r1_tarski(k4_xboole_0(A_76, B_77), B_4))), inference(resolution, [status(thm)], [c_8, c_428])).
% 5.39/2.10  tff(c_440, plain, (![D_78, B_79, A_80]: (~r2_hidden(D_78, B_79) | ~r2_hidden(D_78, k4_xboole_0(A_80, B_79)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.39/2.10  tff(c_2057, plain, (![A_177, B_178, B_179]: (~r2_hidden('#skF_1'(k4_xboole_0(A_177, B_178), B_179), B_178) | r1_tarski(k4_xboole_0(A_177, B_178), B_179))), inference(resolution, [status(thm)], [c_8, c_440])).
% 5.39/2.10  tff(c_2089, plain, (![A_180, B_181]: (r1_tarski(k4_xboole_0(A_180, A_180), B_181))), inference(resolution, [status(thm)], [c_439, c_2057])).
% 5.39/2.10  tff(c_38, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.39/2.10  tff(c_452, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.39/2.10  tff(c_460, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_452])).
% 5.39/2.10  tff(c_2116, plain, (![A_180]: (k4_xboole_0(A_180, A_180)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2089, c_460])).
% 5.39/2.10  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.39/2.10  tff(c_118, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.39/2.10  tff(c_130, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_118])).
% 5.39/2.10  tff(c_273, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.39/2.10  tff(c_288, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_130, c_273])).
% 5.39/2.10  tff(c_2128, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_288])).
% 5.39/2.10  tff(c_131, plain, (![A_53]: (k3_xboole_0(k1_xboole_0, A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_118])).
% 5.39/2.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.39/2.10  tff(c_136, plain, (![A_53]: (k3_xboole_0(A_53, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_131, c_2])).
% 5.39/2.10  tff(c_285, plain, (![A_53]: (k5_xboole_0(A_53, k1_xboole_0)=k4_xboole_0(A_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_273])).
% 5.39/2.10  tff(c_300, plain, (![A_53]: (k4_xboole_0(A_53, k1_xboole_0)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_285])).
% 5.39/2.10  tff(c_645, plain, (![A_104, B_105, C_106]: (k5_xboole_0(k5_xboole_0(A_104, B_105), C_106)=k5_xboole_0(A_104, k5_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.39/2.10  tff(c_48, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.39/2.10  tff(c_2484, plain, (![A_191, B_192, B_193]: (k5_xboole_0(A_191, k5_xboole_0(B_192, k4_xboole_0(B_193, k5_xboole_0(A_191, B_192))))=k2_xboole_0(k5_xboole_0(A_191, B_192), B_193))), inference(superposition, [status(thm), theory('equality')], [c_645, c_48])).
% 5.39/2.10  tff(c_2533, plain, (![B_15, B_193]: (k5_xboole_0(B_15, k5_xboole_0(B_15, k4_xboole_0(B_193, k1_xboole_0)))=k2_xboole_0(k5_xboole_0(B_15, B_15), B_193))), inference(superposition, [status(thm), theory('equality')], [c_2128, c_2484])).
% 5.39/2.10  tff(c_2879, plain, (![B_198, B_199]: (k5_xboole_0(B_198, k5_xboole_0(B_198, B_199))=k2_xboole_0(k1_xboole_0, B_199))), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_300, c_2533])).
% 5.39/2.10  tff(c_2952, plain, (![B_15]: (k5_xboole_0(B_15, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_15))), inference(superposition, [status(thm), theory('equality')], [c_2128, c_2879])).
% 5.39/2.10  tff(c_3019, plain, (![B_15]: (k2_xboole_0(k1_xboole_0, B_15)=B_15)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2952])).
% 5.39/2.10  tff(c_313, plain, (![A_67]: (k4_xboole_0(A_67, k1_xboole_0)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_285])).
% 5.39/2.10  tff(c_323, plain, (![A_67]: (k5_xboole_0(k1_xboole_0, A_67)=k2_xboole_0(k1_xboole_0, A_67))), inference(superposition, [status(thm), theory('equality')], [c_313, c_48])).
% 5.39/2.10  tff(c_3030, plain, (![A_67]: (k5_xboole_0(k1_xboole_0, A_67)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_3019, c_323])).
% 5.39/2.10  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.39/2.10  tff(c_2625, plain, (![B_15, B_193]: (k5_xboole_0(B_15, k5_xboole_0(B_15, B_193))=k2_xboole_0(k1_xboole_0, B_193))), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_300, c_2533])).
% 5.39/2.10  tff(c_3227, plain, (![B_202, B_203]: (k5_xboole_0(B_202, k5_xboole_0(B_202, B_203))=B_203)), inference(demodulation, [status(thm), theory('equality')], [c_3019, c_2625])).
% 5.39/2.10  tff(c_3891, plain, (![A_213, B_214]: (k5_xboole_0(A_213, k2_xboole_0(A_213, B_214))=k4_xboole_0(B_214, A_213))), inference(superposition, [status(thm), theory('equality')], [c_48, c_3227])).
% 5.39/2.10  tff(c_3960, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_3891])).
% 5.39/2.10  tff(c_3973, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_3960])).
% 5.39/2.10  tff(c_2206, plain, (![B_183]: (k5_xboole_0(B_183, B_183)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_288])).
% 5.39/2.10  tff(c_34, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.39/2.10  tff(c_697, plain, (![A_16, B_17, C_106]: (k5_xboole_0(A_16, k5_xboole_0(k3_xboole_0(A_16, B_17), C_106))=k5_xboole_0(k4_xboole_0(A_16, B_17), C_106))), inference(superposition, [status(thm), theory('equality')], [c_34, c_645])).
% 5.39/2.10  tff(c_2212, plain, (![A_16, B_17]: (k5_xboole_0(k4_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k5_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2206, c_697])).
% 5.39/2.10  tff(c_4310, plain, (![A_222, B_223]: (k5_xboole_0(k4_xboole_0(A_222, B_223), k3_xboole_0(A_222, B_223))=A_222)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2212])).
% 5.39/2.10  tff(c_4349, plain, (k5_xboole_0(k1_xboole_0, k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_4')))=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3973, c_4310])).
% 5.39/2.10  tff(c_4397, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3030, c_2, c_4349])).
% 5.39/2.10  tff(c_3325, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3227])).
% 5.39/2.10  tff(c_1342, plain, (![A_140, B_141, B_142]: (r2_hidden('#skF_1'(k4_xboole_0(A_140, B_141), B_142), A_140) | r1_tarski(k4_xboole_0(A_140, B_141), B_142))), inference(resolution, [status(thm)], [c_8, c_428])).
% 5.39/2.10  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.39/2.10  tff(c_1388, plain, (![A_143, B_144]: (r1_tarski(k4_xboole_0(A_143, B_144), A_143))), inference(resolution, [status(thm)], [c_1342, c_6])).
% 5.39/2.10  tff(c_36, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.39/2.10  tff(c_1465, plain, (![A_148, B_149]: (k3_xboole_0(k4_xboole_0(A_148, B_149), A_148)=k4_xboole_0(A_148, B_149))), inference(resolution, [status(thm)], [c_1388, c_36])).
% 5.39/2.10  tff(c_297, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_273])).
% 5.39/2.10  tff(c_1474, plain, (![A_148, B_149]: (k5_xboole_0(A_148, k4_xboole_0(A_148, B_149))=k4_xboole_0(A_148, k4_xboole_0(A_148, B_149)))), inference(superposition, [status(thm), theory('equality')], [c_1465, c_297])).
% 5.39/2.10  tff(c_5557, plain, (![A_251, B_252]: (k4_xboole_0(A_251, k4_xboole_0(A_251, B_252))=k3_xboole_0(A_251, B_252))), inference(demodulation, [status(thm), theory('equality')], [c_3325, c_1474])).
% 5.39/2.10  tff(c_1384, plain, (![A_140, B_141]: (r1_tarski(k4_xboole_0(A_140, B_141), A_140))), inference(resolution, [status(thm)], [c_1342, c_6])).
% 5.39/2.10  tff(c_5701, plain, (![A_255, B_256]: (r1_tarski(k3_xboole_0(A_255, B_256), A_255))), inference(superposition, [status(thm), theory('equality')], [c_5557, c_1384])).
% 5.39/2.10  tff(c_5722, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4397, c_5701])).
% 5.39/2.10  tff(c_58, plain, (![B_42, A_41]: (B_42=A_41 | ~r1_tarski(k1_tarski(A_41), k1_tarski(B_42)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.39/2.10  tff(c_5828, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_5722, c_58])).
% 5.39/2.10  tff(c_5836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_5828])).
% 5.39/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.39/2.10  
% 5.39/2.10  Inference rules
% 5.39/2.10  ----------------------
% 5.39/2.10  #Ref     : 0
% 5.39/2.10  #Sup     : 1376
% 5.39/2.10  #Fact    : 0
% 5.39/2.10  #Define  : 0
% 5.39/2.10  #Split   : 0
% 5.39/2.10  #Chain   : 0
% 5.39/2.10  #Close   : 0
% 5.39/2.10  
% 5.39/2.10  Ordering : KBO
% 5.39/2.10  
% 5.39/2.10  Simplification rules
% 5.39/2.10  ----------------------
% 5.39/2.10  #Subsume      : 52
% 5.39/2.10  #Demod        : 1332
% 5.39/2.10  #Tautology    : 826
% 5.39/2.10  #SimpNegUnit  : 1
% 5.39/2.10  #BackRed      : 16
% 5.39/2.10  
% 5.39/2.10  #Partial instantiations: 0
% 5.39/2.10  #Strategies tried      : 1
% 5.39/2.10  
% 5.39/2.10  Timing (in seconds)
% 5.39/2.10  ----------------------
% 5.39/2.10  Preprocessing        : 0.35
% 5.39/2.10  Parsing              : 0.19
% 5.39/2.10  CNF conversion       : 0.03
% 5.39/2.10  Main loop            : 0.94
% 5.39/2.10  Inferencing          : 0.31
% 5.39/2.10  Reduction            : 0.39
% 5.39/2.10  Demodulation         : 0.32
% 5.39/2.10  BG Simplification    : 0.04
% 5.39/2.10  Subsumption          : 0.14
% 5.39/2.10  Abstraction          : 0.05
% 5.39/2.10  MUC search           : 0.00
% 5.39/2.11  Cooper               : 0.00
% 5.39/2.11  Total                : 1.33
% 5.39/2.11  Index Insertion      : 0.00
% 5.39/2.11  Index Deletion       : 0.00
% 5.39/2.11  Index Matching       : 0.00
% 5.39/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
