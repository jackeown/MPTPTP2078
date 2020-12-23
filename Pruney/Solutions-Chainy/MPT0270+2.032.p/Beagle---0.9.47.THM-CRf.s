%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:57 EST 2020

% Result     : Theorem 7.99s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 508 expanded)
%              Number of leaves         :   35 ( 185 expanded)
%              Depth                    :   19
%              Number of atoms          :  100 ( 557 expanded)
%              Number of equality atoms :   74 ( 423 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_70,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_142,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    ! [B_73,A_74] : k3_xboole_0(B_73,A_74) = k3_xboole_0(A_74,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_66,B_67] : r1_tarski(k3_xboole_0(A_66,B_67),A_66) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,(
    ! [B_67] : k3_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_159,plain,(
    ! [B_73] : k3_xboole_0(B_73,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_112])).

tff(c_332,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_341,plain,(
    ! [B_73] : k5_xboole_0(B_73,k1_xboole_0) = k4_xboole_0(B_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_332])).

tff(c_432,plain,(
    ! [B_110] : k4_xboole_0(B_110,k1_xboole_0) = B_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_341])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_442,plain,(
    ! [B_110] : k4_xboole_0(B_110,B_110) = k3_xboole_0(B_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_18])).

tff(c_455,plain,(
    ! [B_110] : k4_xboole_0(B_110,B_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_442])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_353,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_332])).

tff(c_522,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_353])).

tff(c_745,plain,(
    ! [A_131,B_132,C_133] : k5_xboole_0(k5_xboole_0(A_131,B_132),C_133) = k5_xboole_0(A_131,k5_xboole_0(B_132,C_133)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1113,plain,(
    ! [A_144,C_145] : k5_xboole_0(A_144,k5_xboole_0(A_144,C_145)) = k5_xboole_0(k1_xboole_0,C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_745])).

tff(c_1200,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = k5_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_1113])).

tff(c_1229,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1200])).

tff(c_66,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,k1_tarski(B_59)) = A_58
      | r2_hidden(B_59,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_783,plain,(
    ! [A_3,C_133] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_133)) = k5_xboole_0(k1_xboole_0,C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_745])).

tff(c_1309,plain,(
    ! [A_147,C_148] : k5_xboole_0(A_147,k5_xboole_0(A_147,C_148)) = C_148 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_783])).

tff(c_1856,plain,(
    ! [A_179,B_180] : k5_xboole_0(A_179,k4_xboole_0(A_179,B_180)) = k3_xboole_0(A_179,B_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1309])).

tff(c_1908,plain,(
    ! [A_58,B_59] :
      ( k5_xboole_0(A_58,A_58) = k3_xboole_0(A_58,k1_tarski(B_59))
      | r2_hidden(B_59,A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1856])).

tff(c_1918,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,k1_tarski(B_59)) = k1_xboole_0
      | r2_hidden(B_59,A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_1908])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_347,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_332])).

tff(c_759,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k5_xboole_0(B_132,k5_xboole_0(A_131,B_132))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_522])).

tff(c_1353,plain,(
    ! [B_132,A_131] : k5_xboole_0(B_132,k5_xboole_0(A_131,B_132)) = k5_xboole_0(A_131,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_1309])).

tff(c_1426,plain,(
    ! [B_153,A_154] : k5_xboole_0(B_153,k5_xboole_0(A_154,B_153)) = A_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1353])).

tff(c_3669,plain,(
    ! [A_4142,B_4143] : k5_xboole_0(k3_xboole_0(A_4142,B_4143),k4_xboole_0(B_4143,A_4142)) = B_4143 ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_1426])).

tff(c_3700,plain,(
    ! [B_59,A_58] :
      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(B_59),A_58)) = k1_tarski(B_59)
      | r2_hidden(B_59,A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1918,c_3669])).

tff(c_11305,plain,(
    ! [B_28191,A_28192] :
      ( k4_xboole_0(k1_tarski(B_28191),A_28192) = k1_tarski(B_28191)
      | r2_hidden(B_28191,A_28192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_3700])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_280,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_11393,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11305,c_280])).

tff(c_11457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_11393])).

tff(c_11458,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_11640,plain,(
    ! [A_28480,B_28481] : k5_xboole_0(A_28480,k3_xboole_0(A_28480,B_28481)) = k4_xboole_0(A_28480,B_28481) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11649,plain,(
    ! [B_73] : k5_xboole_0(B_73,k1_xboole_0) = k4_xboole_0(B_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_11640])).

tff(c_11741,plain,(
    ! [B_28488] : k4_xboole_0(B_28488,k1_xboole_0) = B_28488 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_11649])).

tff(c_11761,plain,(
    ! [B_28488] : k4_xboole_0(B_28488,B_28488) = k3_xboole_0(B_28488,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11741,c_18])).

tff(c_11777,plain,(
    ! [B_28488] : k4_xboole_0(B_28488,B_28488) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_11761])).

tff(c_11459,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_11552,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11459,c_72])).

tff(c_11559,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_11552,c_18])).

tff(c_11566,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11559])).

tff(c_11817,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11777,c_11566])).

tff(c_11883,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = k5_xboole_0('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11817,c_12])).

tff(c_11898,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_11883])).

tff(c_64,plain,(
    ! [B_59,A_58] :
      ( ~ r2_hidden(B_59,A_58)
      | k4_xboole_0(A_58,k1_tarski(B_59)) != A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11919,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_11898,c_64])).

tff(c_11936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11458,c_11919])).

tff(c_11937,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_11940,plain,(
    ! [B_28494,A_28495] : k3_xboole_0(B_28494,A_28495) = k3_xboole_0(A_28495,B_28494) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_11956,plain,(
    ! [B_28494] : k3_xboole_0(B_28494,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11940,c_112])).

tff(c_12201,plain,(
    ! [A_28521,B_28522] : k5_xboole_0(A_28521,k3_xboole_0(A_28521,B_28522)) = k4_xboole_0(A_28521,B_28522) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12210,plain,(
    ! [B_28494] : k5_xboole_0(B_28494,k1_xboole_0) = k4_xboole_0(B_28494,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11956,c_12201])).

tff(c_12280,plain,(
    ! [B_28526] : k4_xboole_0(B_28526,k1_xboole_0) = B_28526 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12210])).

tff(c_12300,plain,(
    ! [B_28526] : k4_xboole_0(B_28526,B_28526) = k3_xboole_0(B_28526,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12280,c_18])).

tff(c_12316,plain,(
    ! [B_28526] : k4_xboole_0(B_28526,B_28526) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11956,c_12300])).

tff(c_11938,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12102,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11938,c_74])).

tff(c_12118,plain,(
    ! [A_28512,B_28513] : k4_xboole_0(A_28512,k4_xboole_0(A_28512,B_28513)) = k3_xboole_0(A_28512,B_28513) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12136,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12102,c_12118])).

tff(c_12139,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12136])).

tff(c_12453,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12316,c_12139])).

tff(c_12459,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = k5_xboole_0('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12453,c_12])).

tff(c_12474,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12459])).

tff(c_12495,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12474,c_64])).

tff(c_12512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11937,c_12495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:28:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.99/2.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.99/2.96  
% 7.99/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.99/2.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 7.99/2.96  
% 7.99/2.96  %Foreground sorts:
% 7.99/2.96  
% 7.99/2.96  
% 7.99/2.96  %Background operators:
% 7.99/2.96  
% 7.99/2.96  
% 7.99/2.96  %Foreground operators:
% 7.99/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.99/2.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.99/2.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.99/2.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.99/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.99/2.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.99/2.96  tff('#skF_7', type, '#skF_7': $i).
% 7.99/2.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.99/2.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.99/2.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.99/2.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.99/2.96  tff('#skF_5', type, '#skF_5': $i).
% 7.99/2.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.99/2.96  tff('#skF_6', type, '#skF_6': $i).
% 7.99/2.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.99/2.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.99/2.96  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.99/2.96  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.99/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.99/2.96  tff('#skF_4', type, '#skF_4': $i).
% 7.99/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.99/2.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.99/2.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.99/2.96  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.99/2.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.99/2.96  
% 7.99/2.98  tff(f_103, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 7.99/2.98  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.99/2.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.99/2.98  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.99/2.98  tff(f_55, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.99/2.98  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.99/2.98  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.99/2.98  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.99/2.98  tff(f_63, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.99/2.98  tff(f_97, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.99/2.98  tff(c_70, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.99/2.98  tff(c_142, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 7.99/2.98  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.99/2.98  tff(c_143, plain, (![B_73, A_74]: (k3_xboole_0(B_73, A_74)=k3_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.99/2.98  tff(c_104, plain, (![A_66, B_67]: (r1_tarski(k3_xboole_0(A_66, B_67), A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.99/2.98  tff(c_16, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.99/2.98  tff(c_112, plain, (![B_67]: (k3_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_16])).
% 7.99/2.98  tff(c_159, plain, (![B_73]: (k3_xboole_0(B_73, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_143, c_112])).
% 7.99/2.98  tff(c_332, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.99/2.98  tff(c_341, plain, (![B_73]: (k5_xboole_0(B_73, k1_xboole_0)=k4_xboole_0(B_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_159, c_332])).
% 7.99/2.98  tff(c_432, plain, (![B_110]: (k4_xboole_0(B_110, k1_xboole_0)=B_110)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_341])).
% 7.99/2.98  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.99/2.98  tff(c_442, plain, (![B_110]: (k4_xboole_0(B_110, B_110)=k3_xboole_0(B_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_432, c_18])).
% 7.99/2.98  tff(c_455, plain, (![B_110]: (k4_xboole_0(B_110, B_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_442])).
% 7.99/2.98  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.99/2.98  tff(c_353, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_332])).
% 7.99/2.98  tff(c_522, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_455, c_353])).
% 7.99/2.98  tff(c_745, plain, (![A_131, B_132, C_133]: (k5_xboole_0(k5_xboole_0(A_131, B_132), C_133)=k5_xboole_0(A_131, k5_xboole_0(B_132, C_133)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.99/2.98  tff(c_1113, plain, (![A_144, C_145]: (k5_xboole_0(A_144, k5_xboole_0(A_144, C_145))=k5_xboole_0(k1_xboole_0, C_145))), inference(superposition, [status(thm), theory('equality')], [c_522, c_745])).
% 7.99/2.98  tff(c_1200, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=k5_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_522, c_1113])).
% 7.99/2.98  tff(c_1229, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1200])).
% 7.99/2.98  tff(c_66, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k1_tarski(B_59))=A_58 | r2_hidden(B_59, A_58))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.99/2.98  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.99/2.98  tff(c_783, plain, (![A_3, C_133]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_133))=k5_xboole_0(k1_xboole_0, C_133))), inference(superposition, [status(thm), theory('equality')], [c_522, c_745])).
% 7.99/2.98  tff(c_1309, plain, (![A_147, C_148]: (k5_xboole_0(A_147, k5_xboole_0(A_147, C_148))=C_148)), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_783])).
% 7.99/2.98  tff(c_1856, plain, (![A_179, B_180]: (k5_xboole_0(A_179, k4_xboole_0(A_179, B_180))=k3_xboole_0(A_179, B_180))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1309])).
% 7.99/2.98  tff(c_1908, plain, (![A_58, B_59]: (k5_xboole_0(A_58, A_58)=k3_xboole_0(A_58, k1_tarski(B_59)) | r2_hidden(B_59, A_58))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1856])).
% 7.99/2.98  tff(c_1918, plain, (![A_58, B_59]: (k3_xboole_0(A_58, k1_tarski(B_59))=k1_xboole_0 | r2_hidden(B_59, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_1908])).
% 7.99/2.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.99/2.98  tff(c_347, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_332])).
% 7.99/2.98  tff(c_759, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k5_xboole_0(B_132, k5_xboole_0(A_131, B_132)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_745, c_522])).
% 7.99/2.98  tff(c_1353, plain, (![B_132, A_131]: (k5_xboole_0(B_132, k5_xboole_0(A_131, B_132))=k5_xboole_0(A_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_759, c_1309])).
% 7.99/2.98  tff(c_1426, plain, (![B_153, A_154]: (k5_xboole_0(B_153, k5_xboole_0(A_154, B_153))=A_154)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1353])).
% 7.99/2.98  tff(c_3669, plain, (![A_4142, B_4143]: (k5_xboole_0(k3_xboole_0(A_4142, B_4143), k4_xboole_0(B_4143, A_4142))=B_4143)), inference(superposition, [status(thm), theory('equality')], [c_347, c_1426])).
% 7.99/2.98  tff(c_3700, plain, (![B_59, A_58]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(k1_tarski(B_59), A_58))=k1_tarski(B_59) | r2_hidden(B_59, A_58))), inference(superposition, [status(thm), theory('equality')], [c_1918, c_3669])).
% 7.99/2.98  tff(c_11305, plain, (![B_28191, A_28192]: (k4_xboole_0(k1_tarski(B_28191), A_28192)=k1_tarski(B_28191) | r2_hidden(B_28191, A_28192))), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_3700])).
% 7.99/2.98  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.99/2.98  tff(c_280, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 7.99/2.98  tff(c_11393, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11305, c_280])).
% 7.99/2.98  tff(c_11457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_11393])).
% 7.99/2.98  tff(c_11458, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 7.99/2.98  tff(c_11640, plain, (![A_28480, B_28481]: (k5_xboole_0(A_28480, k3_xboole_0(A_28480, B_28481))=k4_xboole_0(A_28480, B_28481))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.99/2.98  tff(c_11649, plain, (![B_73]: (k5_xboole_0(B_73, k1_xboole_0)=k4_xboole_0(B_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_159, c_11640])).
% 7.99/2.98  tff(c_11741, plain, (![B_28488]: (k4_xboole_0(B_28488, k1_xboole_0)=B_28488)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_11649])).
% 7.99/2.98  tff(c_11761, plain, (![B_28488]: (k4_xboole_0(B_28488, B_28488)=k3_xboole_0(B_28488, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11741, c_18])).
% 7.99/2.98  tff(c_11777, plain, (![B_28488]: (k4_xboole_0(B_28488, B_28488)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_11761])).
% 7.99/2.98  tff(c_11459, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 7.99/2.98  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.99/2.98  tff(c_11552, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11459, c_72])).
% 7.99/2.98  tff(c_11559, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_11552, c_18])).
% 7.99/2.98  tff(c_11566, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11559])).
% 7.99/2.98  tff(c_11817, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11777, c_11566])).
% 7.99/2.98  tff(c_11883, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))=k5_xboole_0('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11817, c_12])).
% 7.99/2.98  tff(c_11898, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_11883])).
% 7.99/2.98  tff(c_64, plain, (![B_59, A_58]: (~r2_hidden(B_59, A_58) | k4_xboole_0(A_58, k1_tarski(B_59))!=A_58)), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.99/2.98  tff(c_11919, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_11898, c_64])).
% 7.99/2.98  tff(c_11936, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11458, c_11919])).
% 7.99/2.98  tff(c_11937, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 7.99/2.98  tff(c_11940, plain, (![B_28494, A_28495]: (k3_xboole_0(B_28494, A_28495)=k3_xboole_0(A_28495, B_28494))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.99/2.98  tff(c_11956, plain, (![B_28494]: (k3_xboole_0(B_28494, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11940, c_112])).
% 7.99/2.98  tff(c_12201, plain, (![A_28521, B_28522]: (k5_xboole_0(A_28521, k3_xboole_0(A_28521, B_28522))=k4_xboole_0(A_28521, B_28522))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.99/2.98  tff(c_12210, plain, (![B_28494]: (k5_xboole_0(B_28494, k1_xboole_0)=k4_xboole_0(B_28494, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11956, c_12201])).
% 7.99/2.98  tff(c_12280, plain, (![B_28526]: (k4_xboole_0(B_28526, k1_xboole_0)=B_28526)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12210])).
% 7.99/2.98  tff(c_12300, plain, (![B_28526]: (k4_xboole_0(B_28526, B_28526)=k3_xboole_0(B_28526, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12280, c_18])).
% 7.99/2.98  tff(c_12316, plain, (![B_28526]: (k4_xboole_0(B_28526, B_28526)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11956, c_12300])).
% 7.99/2.98  tff(c_11938, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 7.99/2.98  tff(c_74, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.99/2.98  tff(c_12102, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11938, c_74])).
% 7.99/2.98  tff(c_12118, plain, (![A_28512, B_28513]: (k4_xboole_0(A_28512, k4_xboole_0(A_28512, B_28513))=k3_xboole_0(A_28512, B_28513))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.99/2.98  tff(c_12136, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12102, c_12118])).
% 7.99/2.98  tff(c_12139, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12136])).
% 7.99/2.98  tff(c_12453, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12316, c_12139])).
% 7.99/2.98  tff(c_12459, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))=k5_xboole_0('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12453, c_12])).
% 7.99/2.98  tff(c_12474, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12459])).
% 7.99/2.98  tff(c_12495, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12474, c_64])).
% 7.99/2.98  tff(c_12512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11937, c_12495])).
% 7.99/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.99/2.98  
% 7.99/2.98  Inference rules
% 7.99/2.98  ----------------------
% 7.99/2.98  #Ref     : 0
% 7.99/2.98  #Sup     : 2357
% 7.99/2.98  #Fact    : 22
% 7.99/2.98  #Define  : 0
% 7.99/2.98  #Split   : 2
% 7.99/2.98  #Chain   : 0
% 7.99/2.98  #Close   : 0
% 7.99/2.98  
% 7.99/2.98  Ordering : KBO
% 7.99/2.98  
% 7.99/2.98  Simplification rules
% 7.99/2.98  ----------------------
% 7.99/2.98  #Subsume      : 250
% 7.99/2.98  #Demod        : 2238
% 7.99/2.98  #Tautology    : 1468
% 7.99/2.98  #SimpNegUnit  : 34
% 7.99/2.98  #BackRed      : 12
% 7.99/2.98  
% 7.99/2.98  #Partial instantiations: 10260
% 7.99/2.98  #Strategies tried      : 1
% 7.99/2.98  
% 7.99/2.98  Timing (in seconds)
% 7.99/2.98  ----------------------
% 7.99/2.98  Preprocessing        : 0.34
% 7.99/2.99  Parsing              : 0.18
% 7.99/2.99  CNF conversion       : 0.02
% 7.99/2.99  Main loop            : 1.86
% 7.99/2.99  Inferencing          : 0.82
% 7.99/2.99  Reduction            : 0.68
% 7.99/2.99  Demodulation         : 0.57
% 7.99/2.99  BG Simplification    : 0.07
% 7.99/2.99  Subsumption          : 0.20
% 7.99/2.99  Abstraction          : 0.09
% 7.99/2.99  MUC search           : 0.00
% 7.99/2.99  Cooper               : 0.00
% 7.99/2.99  Total                : 2.24
% 7.99/2.99  Index Insertion      : 0.00
% 7.99/2.99  Index Deletion       : 0.00
% 7.99/2.99  Index Matching       : 0.00
% 7.99/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
