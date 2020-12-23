%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:46 EST 2020

% Result     : Theorem 36.36s
% Output     : CNFRefutation 36.36s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 693 expanded)
%              Number of leaves         :   44 ( 248 expanded)
%              Depth                    :   17
%              Number of atoms          :  151 ( 998 expanded)
%              Number of equality atoms :   86 ( 548 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_89,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_112,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_117,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_62,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_259,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_xboole_0(A_106,B_107)
      | ~ r2_hidden(C_108,k3_xboole_0(A_106,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_394,plain,(
    ! [A_118,B_119] :
      ( ~ r1_xboole_0(A_118,B_119)
      | k3_xboole_0(A_118,B_119) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_259])).

tff(c_406,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_394])).

tff(c_192,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = A_92
      | ~ r1_xboole_0(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_196,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_497,plain,(
    ! [A_122,B_123] : k4_xboole_0(A_122,k4_xboole_0(A_122,B_123)) = k3_xboole_0(A_122,B_123) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_515,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_497])).

tff(c_518,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_515])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_338,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k3_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_361,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_338])).

tff(c_519,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_361])).

tff(c_78,plain,(
    ! [B_65,A_64] :
      ( k3_xboole_0(B_65,k1_tarski(A_64)) = k1_tarski(A_64)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_861,plain,(
    ! [B_155,A_156] : k5_xboole_0(B_155,k3_xboole_0(A_156,B_155)) = k4_xboole_0(B_155,A_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_338])).

tff(c_878,plain,(
    ! [A_64,B_65] :
      ( k5_xboole_0(k1_tarski(A_64),k1_tarski(A_64)) = k4_xboole_0(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_861])).

tff(c_1226,plain,(
    ! [A_184,B_185] :
      ( k4_xboole_0(k1_tarski(A_184),B_185) = k1_xboole_0
      | ~ r2_hidden(A_184,B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_878])).

tff(c_24,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1246,plain,(
    ! [B_185,A_184] :
      ( k2_xboole_0(B_185,k1_tarski(A_184)) = k5_xboole_0(B_185,k1_xboole_0)
      | ~ r2_hidden(A_184,B_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_24])).

tff(c_1552,plain,(
    ! [B_204,A_205] :
      ( k2_xboole_0(B_204,k1_tarski(A_205)) = B_204
      | ~ r2_hidden(A_205,B_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1246])).

tff(c_80,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_84,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) != k2_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_85,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_84])).

tff(c_1562,plain,
    ( k2_tarski('#skF_7','#skF_8') != k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1552,c_85])).

tff(c_1587,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1562])).

tff(c_52,plain,(
    ! [C_33] : r2_hidden(C_33,k1_tarski(C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_82,plain,(
    ! [A_68,B_69] :
      ( k5_xboole_0(k1_tarski(A_68),k1_tarski(B_69)) = k2_tarski(A_68,B_69)
      | B_69 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_234,plain,(
    ! [A_101,B_102] :
      ( r1_xboole_0(k1_tarski(A_101),B_102)
      | r2_hidden(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1990,plain,(
    ! [A_245,B_246] :
      ( k4_xboole_0(k1_tarski(A_245),B_246) = k1_tarski(A_245)
      | r2_hidden(A_245,B_246) ) ),
    inference(resolution,[status(thm)],[c_234,c_20])).

tff(c_9773,plain,(
    ! [B_9577,A_9578] :
      ( k5_xboole_0(B_9577,k1_tarski(A_9578)) = k2_xboole_0(B_9577,k1_tarski(A_9578))
      | r2_hidden(A_9578,B_9577) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_24])).

tff(c_150803,plain,(
    ! [A_12295,B_12296] :
      ( k2_xboole_0(k1_tarski(A_12295),k1_tarski(B_12296)) = k2_tarski(A_12295,B_12296)
      | r2_hidden(B_12296,k1_tarski(A_12295))
      | B_12296 = A_12295 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_9773])).

tff(c_150822,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_7'))
    | '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_150803,c_85])).

tff(c_150846,plain,(
    '#skF_7' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1587,c_150822])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13451,plain,(
    ! [A_11463,B_11464] :
      ( k3_xboole_0(k1_tarski(A_11463),B_11464) = k1_tarski(A_11463)
      | r2_hidden(A_11463,k4_xboole_0(k1_tarski(A_11463),B_11464)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_14])).

tff(c_1261,plain,(
    ! [A_184,B_15] :
      ( k3_xboole_0(k1_tarski(A_184),B_15) = k1_xboole_0
      | ~ r2_hidden(A_184,k4_xboole_0(k1_tarski(A_184),B_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1226])).

tff(c_13612,plain,(
    ! [A_11469,B_11470] :
      ( k3_xboole_0(k1_tarski(A_11469),B_11470) = k1_xboole_0
      | k3_xboole_0(k1_tarski(A_11469),B_11470) = k1_tarski(A_11469) ) ),
    inference(resolution,[status(thm)],[c_13451,c_1261])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_13843,plain,(
    ! [A_11469,B_11470] :
      ( k5_xboole_0(k1_tarski(A_11469),k1_tarski(A_11469)) = k4_xboole_0(k1_tarski(A_11469),B_11470)
      | k3_xboole_0(k1_tarski(A_11469),B_11470) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13612,c_12])).

tff(c_13976,plain,(
    ! [A_11471,B_11472] :
      ( k4_xboole_0(k1_tarski(A_11471),B_11472) = k1_xboole_0
      | k3_xboole_0(k1_tarski(A_11471),B_11472) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_13843])).

tff(c_14080,plain,(
    ! [B_11472,A_11471] :
      ( k2_xboole_0(B_11472,k1_tarski(A_11471)) = k5_xboole_0(B_11472,k1_xboole_0)
      | k3_xboole_0(k1_tarski(A_11471),B_11472) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13976,c_24])).

tff(c_14171,plain,(
    ! [B_11473,A_11474] :
      ( k2_xboole_0(B_11473,k1_tarski(A_11474)) = B_11473
      | k3_xboole_0(k1_tarski(A_11474),B_11473) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14080])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_274,plain,(
    ! [A_109,C_110] :
      ( ~ r1_xboole_0(A_109,A_109)
      | ~ r2_hidden(C_110,A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_259])).

tff(c_286,plain,(
    ! [C_110,B_19] :
      ( ~ r2_hidden(C_110,B_19)
      | k4_xboole_0(B_19,B_19) != B_19 ) ),
    inference(resolution,[status(thm)],[c_22,c_274])).

tff(c_719,plain,(
    ! [C_135,B_136] :
      ( ~ r2_hidden(C_135,B_136)
      | k1_xboole_0 != B_136 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_286])).

tff(c_747,plain,(
    ! [C_33] : k1_tarski(C_33) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_719])).

tff(c_793,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_1'(A_146,B_147),k3_xboole_0(A_146,B_147))
      | r1_xboole_0(A_146,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_717,plain,(
    ! [C_110,B_19] :
      ( ~ r2_hidden(C_110,B_19)
      | k1_xboole_0 != B_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_286])).

tff(c_838,plain,(
    ! [A_149,B_150] :
      ( k3_xboole_0(A_149,B_150) != k1_xboole_0
      | r1_xboole_0(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_793,c_717])).

tff(c_1588,plain,(
    ! [A_212,B_213] :
      ( k4_xboole_0(A_212,B_213) = A_212
      | k3_xboole_0(A_212,B_213) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_838,c_20])).

tff(c_906,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(k1_tarski(A_64),B_65) = k1_xboole_0
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_878])).

tff(c_1602,plain,(
    ! [A_64,B_213] :
      ( k1_tarski(A_64) = k1_xboole_0
      | ~ r2_hidden(A_64,B_213)
      | k3_xboole_0(k1_tarski(A_64),B_213) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1588,c_906])).

tff(c_1727,plain,(
    ! [A_225,B_226] :
      ( ~ r2_hidden(A_225,B_226)
      | k3_xboole_0(k1_tarski(A_225),B_226) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_1602])).

tff(c_1750,plain,(
    ! [A_225,A_1] :
      ( ~ r2_hidden(A_225,A_1)
      | k3_xboole_0(A_1,k1_tarski(A_225)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1727])).

tff(c_17739,plain,(
    ! [A_11508,A_11509] :
      ( ~ r2_hidden(A_11508,k1_tarski(A_11509))
      | k2_xboole_0(k1_tarski(A_11508),k1_tarski(A_11509)) = k1_tarski(A_11508) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14171,c_1750])).

tff(c_17755,plain,
    ( k2_tarski('#skF_7','#skF_8') != k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17739,c_85])).

tff(c_17781,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_17755])).

tff(c_150850,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150846,c_17781])).

tff(c_150856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150850])).

tff(c_150858,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_17755])).

tff(c_76,plain,(
    ! [A_62,B_63] :
      ( r1_xboole_0(k1_tarski(A_62),B_63)
      | r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1132,plain,(
    ! [A_178,B_179] :
      ( k3_xboole_0(k1_tarski(A_178),B_179) = k1_xboole_0
      | r2_hidden(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_76,c_394])).

tff(c_1175,plain,(
    ! [A_64,A_178] :
      ( k1_tarski(A_64) = k1_xboole_0
      | r2_hidden(A_178,k1_tarski(A_64))
      | ~ r2_hidden(A_64,k1_tarski(A_178)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1132])).

tff(c_1202,plain,(
    ! [A_178,A_64] :
      ( r2_hidden(A_178,k1_tarski(A_64))
      | ~ r2_hidden(A_64,k1_tarski(A_178)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_1175])).

tff(c_150860,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_150858,c_1202])).

tff(c_150870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1587,c_150860])).

tff(c_150872,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1562])).

tff(c_50,plain,(
    ! [C_33,A_29] :
      ( C_33 = A_29
      | ~ r2_hidden(C_33,k1_tarski(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_150883,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_150872,c_50])).

tff(c_150871,plain,(
    k2_tarski('#skF_7','#skF_8') != k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1562])).

tff(c_150884,plain,(
    k2_tarski('#skF_8','#skF_8') != k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150883,c_150883,c_150871])).

tff(c_150889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_150884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.36/28.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.36/28.06  
% 36.36/28.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.36/28.06  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 36.36/28.06  
% 36.36/28.06  %Foreground sorts:
% 36.36/28.06  
% 36.36/28.06  
% 36.36/28.06  %Background operators:
% 36.36/28.06  
% 36.36/28.06  
% 36.36/28.06  %Foreground operators:
% 36.36/28.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 36.36/28.06  tff('#skF_2', type, '#skF_2': $i > $i).
% 36.36/28.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.36/28.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.36/28.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.36/28.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.36/28.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.36/28.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 36.36/28.06  tff('#skF_7', type, '#skF_7': $i).
% 36.36/28.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 36.36/28.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 36.36/28.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.36/28.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 36.36/28.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 36.36/28.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 36.36/28.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 36.36/28.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 36.36/28.06  tff('#skF_8', type, '#skF_8': $i).
% 36.36/28.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.36/28.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 36.36/28.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.36/28.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.36/28.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 36.36/28.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.36/28.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 36.36/28.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.36/28.06  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 36.36/28.06  
% 36.36/28.08  tff(f_89, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 36.36/28.08  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 36.36/28.08  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 36.36/28.08  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 36.36/28.08  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 36.36/28.08  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 36.36/28.08  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 36.36/28.08  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 36.36/28.08  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 36.36/28.08  tff(f_110, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 36.36/28.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 36.36/28.08  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 36.36/28.08  tff(f_112, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 36.36/28.08  tff(f_120, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 36.36/28.08  tff(f_87, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 36.36/28.08  tff(f_117, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 36.36/28.08  tff(f_106, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 36.36/28.08  tff(c_62, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_89])).
% 36.36/28.08  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.36/28.08  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.36/28.08  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.36/28.08  tff(c_259, plain, (![A_106, B_107, C_108]: (~r1_xboole_0(A_106, B_107) | ~r2_hidden(C_108, k3_xboole_0(A_106, B_107)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.36/28.08  tff(c_394, plain, (![A_118, B_119]: (~r1_xboole_0(A_118, B_119) | k3_xboole_0(A_118, B_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_259])).
% 36.36/28.08  tff(c_406, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_394])).
% 36.36/28.08  tff(c_192, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=A_92 | ~r1_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_63])).
% 36.36/28.08  tff(c_196, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(resolution, [status(thm)], [c_18, c_192])).
% 36.36/28.08  tff(c_497, plain, (![A_122, B_123]: (k4_xboole_0(A_122, k4_xboole_0(A_122, B_123))=k3_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_55])).
% 36.36/28.08  tff(c_515, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_196, c_497])).
% 36.36/28.08  tff(c_518, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_406, c_515])).
% 36.36/28.08  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 36.36/28.08  tff(c_338, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k3_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.36/28.08  tff(c_361, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_338])).
% 36.36/28.08  tff(c_519, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_518, c_361])).
% 36.36/28.08  tff(c_78, plain, (![B_65, A_64]: (k3_xboole_0(B_65, k1_tarski(A_64))=k1_tarski(A_64) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.36/28.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.36/28.08  tff(c_861, plain, (![B_155, A_156]: (k5_xboole_0(B_155, k3_xboole_0(A_156, B_155))=k4_xboole_0(B_155, A_156))), inference(superposition, [status(thm), theory('equality')], [c_2, c_338])).
% 36.36/28.08  tff(c_878, plain, (![A_64, B_65]: (k5_xboole_0(k1_tarski(A_64), k1_tarski(A_64))=k4_xboole_0(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_78, c_861])).
% 36.36/28.08  tff(c_1226, plain, (![A_184, B_185]: (k4_xboole_0(k1_tarski(A_184), B_185)=k1_xboole_0 | ~r2_hidden(A_184, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_878])).
% 36.36/28.08  tff(c_24, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 36.36/28.08  tff(c_1246, plain, (![B_185, A_184]: (k2_xboole_0(B_185, k1_tarski(A_184))=k5_xboole_0(B_185, k1_xboole_0) | ~r2_hidden(A_184, B_185))), inference(superposition, [status(thm), theory('equality')], [c_1226, c_24])).
% 36.36/28.08  tff(c_1552, plain, (![B_204, A_205]: (k2_xboole_0(B_204, k1_tarski(A_205))=B_204 | ~r2_hidden(A_205, B_204))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1246])).
% 36.36/28.08  tff(c_80, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_112])).
% 36.36/28.08  tff(c_84, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8')))!=k2_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 36.36/28.08  tff(c_85, plain, (k2_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_84])).
% 36.36/28.08  tff(c_1562, plain, (k2_tarski('#skF_7', '#skF_8')!=k1_tarski('#skF_7') | ~r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1552, c_85])).
% 36.36/28.08  tff(c_1587, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_1562])).
% 36.36/28.08  tff(c_52, plain, (![C_33]: (r2_hidden(C_33, k1_tarski(C_33)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 36.36/28.08  tff(c_82, plain, (![A_68, B_69]: (k5_xboole_0(k1_tarski(A_68), k1_tarski(B_69))=k2_tarski(A_68, B_69) | B_69=A_68)), inference(cnfTransformation, [status(thm)], [f_117])).
% 36.36/28.08  tff(c_234, plain, (![A_101, B_102]: (r1_xboole_0(k1_tarski(A_101), B_102) | r2_hidden(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_106])).
% 36.36/28.08  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 36.36/28.08  tff(c_1990, plain, (![A_245, B_246]: (k4_xboole_0(k1_tarski(A_245), B_246)=k1_tarski(A_245) | r2_hidden(A_245, B_246))), inference(resolution, [status(thm)], [c_234, c_20])).
% 36.36/28.08  tff(c_9773, plain, (![B_9577, A_9578]: (k5_xboole_0(B_9577, k1_tarski(A_9578))=k2_xboole_0(B_9577, k1_tarski(A_9578)) | r2_hidden(A_9578, B_9577))), inference(superposition, [status(thm), theory('equality')], [c_1990, c_24])).
% 36.36/28.08  tff(c_150803, plain, (![A_12295, B_12296]: (k2_xboole_0(k1_tarski(A_12295), k1_tarski(B_12296))=k2_tarski(A_12295, B_12296) | r2_hidden(B_12296, k1_tarski(A_12295)) | B_12296=A_12295)), inference(superposition, [status(thm), theory('equality')], [c_82, c_9773])).
% 36.36/28.08  tff(c_150822, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7')) | '#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_150803, c_85])).
% 36.36/28.08  tff(c_150846, plain, ('#skF_7'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1587, c_150822])).
% 36.36/28.08  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 36.36/28.08  tff(c_13451, plain, (![A_11463, B_11464]: (k3_xboole_0(k1_tarski(A_11463), B_11464)=k1_tarski(A_11463) | r2_hidden(A_11463, k4_xboole_0(k1_tarski(A_11463), B_11464)))), inference(superposition, [status(thm), theory('equality')], [c_1990, c_14])).
% 36.36/28.08  tff(c_1261, plain, (![A_184, B_15]: (k3_xboole_0(k1_tarski(A_184), B_15)=k1_xboole_0 | ~r2_hidden(A_184, k4_xboole_0(k1_tarski(A_184), B_15)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1226])).
% 36.36/28.08  tff(c_13612, plain, (![A_11469, B_11470]: (k3_xboole_0(k1_tarski(A_11469), B_11470)=k1_xboole_0 | k3_xboole_0(k1_tarski(A_11469), B_11470)=k1_tarski(A_11469))), inference(resolution, [status(thm)], [c_13451, c_1261])).
% 36.36/28.08  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.36/28.08  tff(c_13843, plain, (![A_11469, B_11470]: (k5_xboole_0(k1_tarski(A_11469), k1_tarski(A_11469))=k4_xboole_0(k1_tarski(A_11469), B_11470) | k3_xboole_0(k1_tarski(A_11469), B_11470)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13612, c_12])).
% 36.36/28.08  tff(c_13976, plain, (![A_11471, B_11472]: (k4_xboole_0(k1_tarski(A_11471), B_11472)=k1_xboole_0 | k3_xboole_0(k1_tarski(A_11471), B_11472)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_519, c_13843])).
% 36.36/28.08  tff(c_14080, plain, (![B_11472, A_11471]: (k2_xboole_0(B_11472, k1_tarski(A_11471))=k5_xboole_0(B_11472, k1_xboole_0) | k3_xboole_0(k1_tarski(A_11471), B_11472)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13976, c_24])).
% 36.36/28.08  tff(c_14171, plain, (![B_11473, A_11474]: (k2_xboole_0(B_11473, k1_tarski(A_11474))=B_11473 | k3_xboole_0(k1_tarski(A_11474), B_11473)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14080])).
% 36.36/28.08  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 36.36/28.08  tff(c_274, plain, (![A_109, C_110]: (~r1_xboole_0(A_109, A_109) | ~r2_hidden(C_110, A_109))), inference(superposition, [status(thm), theory('equality')], [c_4, c_259])).
% 36.36/28.08  tff(c_286, plain, (![C_110, B_19]: (~r2_hidden(C_110, B_19) | k4_xboole_0(B_19, B_19)!=B_19)), inference(resolution, [status(thm)], [c_22, c_274])).
% 36.36/28.08  tff(c_719, plain, (![C_135, B_136]: (~r2_hidden(C_135, B_136) | k1_xboole_0!=B_136)), inference(demodulation, [status(thm), theory('equality')], [c_518, c_286])).
% 36.36/28.08  tff(c_747, plain, (![C_33]: (k1_tarski(C_33)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_719])).
% 36.36/28.08  tff(c_793, plain, (![A_146, B_147]: (r2_hidden('#skF_1'(A_146, B_147), k3_xboole_0(A_146, B_147)) | r1_xboole_0(A_146, B_147))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.36/28.08  tff(c_717, plain, (![C_110, B_19]: (~r2_hidden(C_110, B_19) | k1_xboole_0!=B_19)), inference(demodulation, [status(thm), theory('equality')], [c_518, c_286])).
% 36.36/28.08  tff(c_838, plain, (![A_149, B_150]: (k3_xboole_0(A_149, B_150)!=k1_xboole_0 | r1_xboole_0(A_149, B_150))), inference(resolution, [status(thm)], [c_793, c_717])).
% 36.36/28.08  tff(c_1588, plain, (![A_212, B_213]: (k4_xboole_0(A_212, B_213)=A_212 | k3_xboole_0(A_212, B_213)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_838, c_20])).
% 36.36/28.08  tff(c_906, plain, (![A_64, B_65]: (k4_xboole_0(k1_tarski(A_64), B_65)=k1_xboole_0 | ~r2_hidden(A_64, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_878])).
% 36.36/28.08  tff(c_1602, plain, (![A_64, B_213]: (k1_tarski(A_64)=k1_xboole_0 | ~r2_hidden(A_64, B_213) | k3_xboole_0(k1_tarski(A_64), B_213)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1588, c_906])).
% 36.36/28.08  tff(c_1727, plain, (![A_225, B_226]: (~r2_hidden(A_225, B_226) | k3_xboole_0(k1_tarski(A_225), B_226)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_747, c_1602])).
% 36.36/28.08  tff(c_1750, plain, (![A_225, A_1]: (~r2_hidden(A_225, A_1) | k3_xboole_0(A_1, k1_tarski(A_225))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1727])).
% 36.36/28.08  tff(c_17739, plain, (![A_11508, A_11509]: (~r2_hidden(A_11508, k1_tarski(A_11509)) | k2_xboole_0(k1_tarski(A_11508), k1_tarski(A_11509))=k1_tarski(A_11508))), inference(superposition, [status(thm), theory('equality')], [c_14171, c_1750])).
% 36.36/28.08  tff(c_17755, plain, (k2_tarski('#skF_7', '#skF_8')!=k1_tarski('#skF_7') | ~r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_17739, c_85])).
% 36.36/28.08  tff(c_17781, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_17755])).
% 36.36/28.08  tff(c_150850, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_150846, c_17781])).
% 36.36/28.08  tff(c_150856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_150850])).
% 36.36/28.08  tff(c_150858, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_17755])).
% 36.36/28.08  tff(c_76, plain, (![A_62, B_63]: (r1_xboole_0(k1_tarski(A_62), B_63) | r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_106])).
% 36.36/28.08  tff(c_1132, plain, (![A_178, B_179]: (k3_xboole_0(k1_tarski(A_178), B_179)=k1_xboole_0 | r2_hidden(A_178, B_179))), inference(resolution, [status(thm)], [c_76, c_394])).
% 36.36/28.08  tff(c_1175, plain, (![A_64, A_178]: (k1_tarski(A_64)=k1_xboole_0 | r2_hidden(A_178, k1_tarski(A_64)) | ~r2_hidden(A_64, k1_tarski(A_178)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1132])).
% 36.36/28.08  tff(c_1202, plain, (![A_178, A_64]: (r2_hidden(A_178, k1_tarski(A_64)) | ~r2_hidden(A_64, k1_tarski(A_178)))), inference(negUnitSimplification, [status(thm)], [c_747, c_1175])).
% 36.36/28.08  tff(c_150860, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_150858, c_1202])).
% 36.36/28.08  tff(c_150870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1587, c_150860])).
% 36.36/28.08  tff(c_150872, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_1562])).
% 36.36/28.08  tff(c_50, plain, (![C_33, A_29]: (C_33=A_29 | ~r2_hidden(C_33, k1_tarski(A_29)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 36.36/28.08  tff(c_150883, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_150872, c_50])).
% 36.36/28.08  tff(c_150871, plain, (k2_tarski('#skF_7', '#skF_8')!=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_1562])).
% 36.36/28.08  tff(c_150884, plain, (k2_tarski('#skF_8', '#skF_8')!=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_150883, c_150883, c_150871])).
% 36.36/28.08  tff(c_150889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_150884])).
% 36.36/28.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.36/28.08  
% 36.36/28.08  Inference rules
% 36.36/28.08  ----------------------
% 36.36/28.08  #Ref     : 1
% 36.36/28.08  #Sup     : 35664
% 36.36/28.08  #Fact    : 126
% 36.36/28.08  #Define  : 0
% 36.36/28.08  #Split   : 4
% 36.36/28.08  #Chain   : 0
% 36.36/28.08  #Close   : 0
% 36.36/28.08  
% 36.36/28.08  Ordering : KBO
% 36.36/28.08  
% 36.36/28.08  Simplification rules
% 36.36/28.08  ----------------------
% 36.36/28.08  #Subsume      : 16371
% 36.36/28.08  #Demod        : 33715
% 36.36/28.08  #Tautology    : 10186
% 36.36/28.08  #SimpNegUnit  : 2267
% 36.36/28.08  #BackRed      : 10
% 36.36/28.08  
% 36.36/28.08  #Partial instantiations: 4004
% 36.36/28.08  #Strategies tried      : 1
% 36.36/28.08  
% 36.36/28.08  Timing (in seconds)
% 36.36/28.08  ----------------------
% 36.36/28.08  Preprocessing        : 0.34
% 36.36/28.08  Parsing              : 0.17
% 36.36/28.08  CNF conversion       : 0.03
% 36.36/28.08  Main loop            : 26.94
% 36.36/28.08  Inferencing          : 4.00
% 36.36/28.08  Reduction            : 9.91
% 36.36/28.08  Demodulation         : 8.09
% 36.36/28.08  BG Simplification    : 0.47
% 36.36/28.08  Subsumption          : 11.66
% 36.36/28.08  Abstraction          : 1.09
% 36.36/28.08  MUC search           : 0.00
% 36.36/28.08  Cooper               : 0.00
% 36.36/28.08  Total                : 27.32
% 36.36/28.08  Index Insertion      : 0.00
% 36.36/28.08  Index Deletion       : 0.00
% 36.36/28.08  Index Matching       : 0.00
% 36.36/28.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
