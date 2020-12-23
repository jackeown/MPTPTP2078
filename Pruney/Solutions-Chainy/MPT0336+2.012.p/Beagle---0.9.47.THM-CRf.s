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
% DateTime   : Thu Dec  3 09:55:02 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 224 expanded)
%              Number of leaves         :   33 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  150 ( 388 expanded)
%              Number of equality atoms :   40 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_77,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_362,plain,(
    ! [A_64,B_65] :
      ( r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_368,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_362,c_42])).

tff(c_371,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_368])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1079,plain,(
    ! [A_113,B_114,C_115] : k3_xboole_0(k3_xboole_0(A_113,B_114),C_115) = k3_xboole_0(A_113,k3_xboole_0(B_114,C_115)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1187,plain,(
    ! [A_7,C_115] : k3_xboole_0(A_7,k3_xboole_0(A_7,C_115)) = k3_xboole_0(A_7,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1079])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_170,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_182,plain,(
    ! [A_26] : k3_xboole_0(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_170])).

tff(c_374,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_391,plain,(
    ! [A_26,C_72] :
      ( ~ r1_xboole_0(A_26,k1_xboole_0)
      | ~ r2_hidden(C_72,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_374])).

tff(c_410,plain,(
    ! [C_72] : ~ r2_hidden(C_72,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_391])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_1'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_431,plain,(
    ! [A_75,C_76] :
      ( ~ r1_xboole_0(A_75,A_75)
      | ~ r2_hidden(C_76,A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_374])).

tff(c_437,plain,(
    ! [C_76,B_6] :
      ( ~ r2_hidden(C_76,B_6)
      | k3_xboole_0(B_6,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_431])).

tff(c_450,plain,(
    ! [C_77,B_78] :
      ( ~ r2_hidden(C_77,B_78)
      | k1_xboole_0 != B_78 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_437])).

tff(c_465,plain,(
    ! [B_79,A_80] :
      ( k1_xboole_0 != B_79
      | r1_xboole_0(A_80,B_79) ) ),
    inference(resolution,[status(thm)],[c_14,c_450])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_519,plain,(
    ! [A_80] : k3_xboole_0(A_80,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_465,c_6])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_2'(A_14,B_15),k3_xboole_0(A_14,B_15))
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_1'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_489,plain,(
    ! [A_84,B_85] :
      ( k1_xboole_0 != A_84
      | r1_xboole_0(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_16,c_450])).

tff(c_608,plain,(
    ! [B_85] : k3_xboole_0(k1_xboole_0,B_85) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_489,c_6])).

tff(c_44,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_181,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_170])).

tff(c_1170,plain,(
    ! [C_115] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',C_115)) = k3_xboole_0(k1_xboole_0,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1079])).

tff(c_1203,plain,(
    ! [C_115] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',C_115)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_1170])).

tff(c_40,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_976,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_xboole_0(A_106,B_107)
      | ~ r2_hidden(C_108,k3_xboole_0(B_107,A_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_374])).

tff(c_1030,plain,(
    ! [B_109,A_110] :
      ( ~ r1_xboole_0(B_109,A_110)
      | r1_xboole_0(A_110,B_109) ) ),
    inference(resolution,[status(thm)],[c_18,c_976])).

tff(c_1051,plain,(
    ! [B_40,A_39] :
      ( r1_xboole_0(B_40,k1_tarski(A_39))
      | r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_40,c_1030])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_311,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_330,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_49,c_311])).

tff(c_878,plain,(
    ! [A_99,B_100,B_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | r1_xboole_0(k3_xboole_0(A_99,B_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_16,c_374])).

tff(c_901,plain,(
    ! [B_101] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6'))
      | r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_878])).

tff(c_5754,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_901])).

tff(c_5779,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1051,c_5754])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_697,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,B_91)
      | ~ r2_hidden(C_92,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6868,plain,(
    ! [C_196,B_197,A_198] :
      ( ~ r2_hidden(C_196,B_197)
      | ~ r2_hidden(C_196,A_198)
      | k3_xboole_0(A_198,B_197) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_697])).

tff(c_6890,plain,(
    ! [A_199] :
      ( ~ r2_hidden('#skF_6',A_199)
      | k3_xboole_0(A_199,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_6868])).

tff(c_6893,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5779,c_6890])).

tff(c_6904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_4,c_6893])).

tff(c_6905,plain,(
    ! [B_101] : r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_101) ),
    inference(splitRight,[status(thm)],[c_901])).

tff(c_385,plain,(
    ! [C_72] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6'))
      | ~ r2_hidden(C_72,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_374])).

tff(c_6985,plain,(
    ! [C_202] : ~ r2_hidden(C_202,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6905,c_385])).

tff(c_7010,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_6985])).

tff(c_7024,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7010,c_6])).

tff(c_1122,plain,(
    ! [C_115,A_113,B_114] : k3_xboole_0(C_115,k3_xboole_0(A_113,B_114)) = k3_xboole_0(A_113,k3_xboole_0(B_114,C_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_4])).

tff(c_7060,plain,(
    ! [A_113] : k3_xboole_0('#skF_3',k3_xboole_0(A_113,'#skF_4')) = k3_xboole_0(A_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7024,c_1122])).

tff(c_7448,plain,(
    ! [A_207] : k3_xboole_0('#skF_3',k3_xboole_0(A_207,'#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_7060])).

tff(c_736,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_2'(A_95,B_96),k3_xboole_0(A_95,B_96))
      | r1_xboole_0(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_763,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4),k3_xboole_0(B_4,A_3))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_736])).

tff(c_7453,plain,(
    ! [A_207] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_207,'#skF_4'),'#skF_3'),k1_xboole_0)
      | r1_xboole_0(k3_xboole_0(A_207,'#skF_4'),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7448,c_763])).

tff(c_7606,plain,(
    ! [A_207] : r1_xboole_0(k3_xboole_0(A_207,'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_7453])).

tff(c_24,plain,(
    ! [A_22,B_23] : r1_tarski(k3_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1631,plain,(
    ! [A_128,B_129,C_130] :
      ( r1_tarski(A_128,B_129)
      | ~ r1_xboole_0(A_128,C_130)
      | ~ r1_tarski(A_128,k2_xboole_0(B_129,C_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14035,plain,(
    ! [B_284,C_285,B_286] :
      ( r1_tarski(k3_xboole_0(k2_xboole_0(B_284,C_285),B_286),B_284)
      | ~ r1_xboole_0(k3_xboole_0(k2_xboole_0(B_284,C_285),B_286),C_285) ) ),
    inference(resolution,[status(thm)],[c_24,c_1631])).

tff(c_14059,plain,(
    ! [B_284] : r1_tarski(k3_xboole_0(k2_xboole_0(B_284,'#skF_3'),'#skF_4'),B_284) ),
    inference(resolution,[status(thm)],[c_7606,c_14035])).

tff(c_14179,plain,(
    ! [B_287] : r1_tarski(k3_xboole_0('#skF_4',k2_xboole_0(B_287,'#skF_3')),B_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14059])).

tff(c_463,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_450])).

tff(c_202,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_181])).

tff(c_1452,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r1_xboole_0(A_121,k3_xboole_0(B_122,C_123))
      | ~ r1_tarski(A_121,C_123)
      | r1_xboole_0(A_121,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1502,plain,(
    ! [A_121] :
      ( ~ r1_xboole_0(A_121,k1_xboole_0)
      | ~ r1_tarski(A_121,'#skF_5')
      | r1_xboole_0(A_121,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_1452])).

tff(c_1540,plain,(
    ! [A_124] :
      ( ~ r1_tarski(A_124,'#skF_5')
      | r1_xboole_0(A_124,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_1502])).

tff(c_1023,plain,(
    ! [B_15,A_14] :
      ( ~ r1_xboole_0(B_15,A_14)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_976])).

tff(c_1583,plain,(
    ! [A_126] :
      ( r1_xboole_0('#skF_4',A_126)
      | ~ r1_tarski(A_126,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1540,c_1023])).

tff(c_1606,plain,(
    ! [A_126] :
      ( k3_xboole_0('#skF_4',A_126) = k1_xboole_0
      | ~ r1_tarski(A_126,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1583,c_6])).

tff(c_14206,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_3'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14179,c_1606])).

tff(c_14250,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_2,c_14206])).

tff(c_14252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_14250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n022.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:13:11 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.93/2.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.93/2.92  
% 7.93/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.93/2.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.93/2.92  
% 7.93/2.92  %Foreground sorts:
% 7.93/2.92  
% 7.93/2.92  
% 7.93/2.92  %Background operators:
% 7.93/2.92  
% 7.93/2.92  
% 7.93/2.92  %Foreground operators:
% 7.93/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.93/2.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.93/2.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.93/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.93/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.93/2.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.93/2.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.93/2.92  tff('#skF_5', type, '#skF_5': $i).
% 7.93/2.92  tff('#skF_6', type, '#skF_6': $i).
% 7.93/2.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.93/2.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.93/2.92  tff('#skF_3', type, '#skF_3': $i).
% 7.93/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.93/2.92  tff('#skF_4', type, '#skF_4': $i).
% 7.93/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.93/2.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.93/2.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.93/2.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.93/2.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.93/2.92  
% 7.93/2.94  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.93/2.94  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.93/2.94  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.93/2.94  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.93/2.94  tff(f_69, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.93/2.94  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.93/2.94  tff(f_77, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.93/2.94  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.93/2.94  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.93/2.94  tff(f_102, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.93/2.94  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.93/2.94  tff(f_71, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.93/2.94  tff(f_83, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 7.93/2.94  tff(f_91, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 7.93/2.94  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.93/2.94  tff(c_362, plain, (![A_64, B_65]: (r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.93/2.94  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.93/2.94  tff(c_368, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_362, c_42])).
% 7.93/2.94  tff(c_371, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_368])).
% 7.93/2.94  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.93/2.94  tff(c_1079, plain, (![A_113, B_114, C_115]: (k3_xboole_0(k3_xboole_0(A_113, B_114), C_115)=k3_xboole_0(A_113, k3_xboole_0(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.93/2.94  tff(c_1187, plain, (![A_7, C_115]: (k3_xboole_0(A_7, k3_xboole_0(A_7, C_115))=k3_xboole_0(A_7, C_115))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1079])).
% 7.93/2.94  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.93/2.94  tff(c_28, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.93/2.94  tff(c_170, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.93/2.94  tff(c_182, plain, (![A_26]: (k3_xboole_0(A_26, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_170])).
% 7.93/2.94  tff(c_374, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.93/2.94  tff(c_391, plain, (![A_26, C_72]: (~r1_xboole_0(A_26, k1_xboole_0) | ~r2_hidden(C_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_182, c_374])).
% 7.93/2.94  tff(c_410, plain, (![C_72]: (~r2_hidden(C_72, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_391])).
% 7.93/2.94  tff(c_14, plain, (![A_9, B_10]: (r2_hidden('#skF_1'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.93/2.94  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.93/2.94  tff(c_431, plain, (![A_75, C_76]: (~r1_xboole_0(A_75, A_75) | ~r2_hidden(C_76, A_75))), inference(superposition, [status(thm), theory('equality')], [c_10, c_374])).
% 7.93/2.94  tff(c_437, plain, (![C_76, B_6]: (~r2_hidden(C_76, B_6) | k3_xboole_0(B_6, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_431])).
% 7.93/2.94  tff(c_450, plain, (![C_77, B_78]: (~r2_hidden(C_77, B_78) | k1_xboole_0!=B_78)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_437])).
% 7.93/2.94  tff(c_465, plain, (![B_79, A_80]: (k1_xboole_0!=B_79 | r1_xboole_0(A_80, B_79))), inference(resolution, [status(thm)], [c_14, c_450])).
% 7.93/2.94  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.93/2.94  tff(c_519, plain, (![A_80]: (k3_xboole_0(A_80, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_465, c_6])).
% 7.93/2.94  tff(c_18, plain, (![A_14, B_15]: (r2_hidden('#skF_2'(A_14, B_15), k3_xboole_0(A_14, B_15)) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.93/2.94  tff(c_16, plain, (![A_9, B_10]: (r2_hidden('#skF_1'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.93/2.94  tff(c_489, plain, (![A_84, B_85]: (k1_xboole_0!=A_84 | r1_xboole_0(A_84, B_85))), inference(resolution, [status(thm)], [c_16, c_450])).
% 7.93/2.94  tff(c_608, plain, (![B_85]: (k3_xboole_0(k1_xboole_0, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_489, c_6])).
% 7.93/2.94  tff(c_44, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.93/2.94  tff(c_181, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_170])).
% 7.93/2.94  tff(c_1170, plain, (![C_115]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', C_115))=k3_xboole_0(k1_xboole_0, C_115))), inference(superposition, [status(thm), theory('equality')], [c_181, c_1079])).
% 7.93/2.94  tff(c_1203, plain, (![C_115]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', C_115))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_608, c_1170])).
% 7.93/2.94  tff(c_40, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.93/2.94  tff(c_976, plain, (![A_106, B_107, C_108]: (~r1_xboole_0(A_106, B_107) | ~r2_hidden(C_108, k3_xboole_0(B_107, A_106)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_374])).
% 7.93/2.94  tff(c_1030, plain, (![B_109, A_110]: (~r1_xboole_0(B_109, A_110) | r1_xboole_0(A_110, B_109))), inference(resolution, [status(thm)], [c_18, c_976])).
% 7.93/2.94  tff(c_1051, plain, (![B_40, A_39]: (r1_xboole_0(B_40, k1_tarski(A_39)) | r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_40, c_1030])).
% 7.93/2.94  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.93/2.94  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_48])).
% 7.93/2.94  tff(c_311, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.93/2.94  tff(c_330, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_49, c_311])).
% 7.93/2.94  tff(c_878, plain, (![A_99, B_100, B_101]: (~r1_xboole_0(A_99, B_100) | r1_xboole_0(k3_xboole_0(A_99, B_100), B_101))), inference(resolution, [status(thm)], [c_16, c_374])).
% 7.93/2.94  tff(c_901, plain, (![B_101]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6')) | r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_101))), inference(superposition, [status(thm), theory('equality')], [c_330, c_878])).
% 7.93/2.94  tff(c_5754, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_901])).
% 7.93/2.94  tff(c_5779, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1051, c_5754])).
% 7.93/2.94  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.93/2.94  tff(c_697, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, B_91) | ~r2_hidden(C_92, A_90))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.93/2.94  tff(c_6868, plain, (![C_196, B_197, A_198]: (~r2_hidden(C_196, B_197) | ~r2_hidden(C_196, A_198) | k3_xboole_0(A_198, B_197)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_697])).
% 7.93/2.94  tff(c_6890, plain, (![A_199]: (~r2_hidden('#skF_6', A_199) | k3_xboole_0(A_199, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_6868])).
% 7.93/2.94  tff(c_6893, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_5779, c_6890])).
% 7.93/2.94  tff(c_6904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1203, c_4, c_6893])).
% 7.93/2.94  tff(c_6905, plain, (![B_101]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_101))), inference(splitRight, [status(thm)], [c_901])).
% 7.93/2.94  tff(c_385, plain, (![C_72]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6')) | ~r2_hidden(C_72, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_330, c_374])).
% 7.93/2.94  tff(c_6985, plain, (![C_202]: (~r2_hidden(C_202, k3_xboole_0('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6905, c_385])).
% 7.93/2.94  tff(c_7010, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_6985])).
% 7.93/2.94  tff(c_7024, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_7010, c_6])).
% 7.93/2.94  tff(c_1122, plain, (![C_115, A_113, B_114]: (k3_xboole_0(C_115, k3_xboole_0(A_113, B_114))=k3_xboole_0(A_113, k3_xboole_0(B_114, C_115)))), inference(superposition, [status(thm), theory('equality')], [c_1079, c_4])).
% 7.93/2.94  tff(c_7060, plain, (![A_113]: (k3_xboole_0('#skF_3', k3_xboole_0(A_113, '#skF_4'))=k3_xboole_0(A_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7024, c_1122])).
% 7.93/2.94  tff(c_7448, plain, (![A_207]: (k3_xboole_0('#skF_3', k3_xboole_0(A_207, '#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_519, c_7060])).
% 7.93/2.94  tff(c_736, plain, (![A_95, B_96]: (r2_hidden('#skF_2'(A_95, B_96), k3_xboole_0(A_95, B_96)) | r1_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.93/2.94  tff(c_763, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4), k3_xboole_0(B_4, A_3)) | r1_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_736])).
% 7.93/2.94  tff(c_7453, plain, (![A_207]: (r2_hidden('#skF_2'(k3_xboole_0(A_207, '#skF_4'), '#skF_3'), k1_xboole_0) | r1_xboole_0(k3_xboole_0(A_207, '#skF_4'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7448, c_763])).
% 7.93/2.94  tff(c_7606, plain, (![A_207]: (r1_xboole_0(k3_xboole_0(A_207, '#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_410, c_7453])).
% 7.93/2.94  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(k3_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.93/2.94  tff(c_1631, plain, (![A_128, B_129, C_130]: (r1_tarski(A_128, B_129) | ~r1_xboole_0(A_128, C_130) | ~r1_tarski(A_128, k2_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.93/2.94  tff(c_14035, plain, (![B_284, C_285, B_286]: (r1_tarski(k3_xboole_0(k2_xboole_0(B_284, C_285), B_286), B_284) | ~r1_xboole_0(k3_xboole_0(k2_xboole_0(B_284, C_285), B_286), C_285))), inference(resolution, [status(thm)], [c_24, c_1631])).
% 7.93/2.94  tff(c_14059, plain, (![B_284]: (r1_tarski(k3_xboole_0(k2_xboole_0(B_284, '#skF_3'), '#skF_4'), B_284))), inference(resolution, [status(thm)], [c_7606, c_14035])).
% 7.93/2.94  tff(c_14179, plain, (![B_287]: (r1_tarski(k3_xboole_0('#skF_4', k2_xboole_0(B_287, '#skF_3')), B_287))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14059])).
% 7.93/2.94  tff(c_463, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_450])).
% 7.93/2.94  tff(c_202, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_181])).
% 7.93/2.94  tff(c_1452, plain, (![A_121, B_122, C_123]: (~r1_xboole_0(A_121, k3_xboole_0(B_122, C_123)) | ~r1_tarski(A_121, C_123) | r1_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.93/2.94  tff(c_1502, plain, (![A_121]: (~r1_xboole_0(A_121, k1_xboole_0) | ~r1_tarski(A_121, '#skF_5') | r1_xboole_0(A_121, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_1452])).
% 7.93/2.94  tff(c_1540, plain, (![A_124]: (~r1_tarski(A_124, '#skF_5') | r1_xboole_0(A_124, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_1502])).
% 7.93/2.94  tff(c_1023, plain, (![B_15, A_14]: (~r1_xboole_0(B_15, A_14) | r1_xboole_0(A_14, B_15))), inference(resolution, [status(thm)], [c_18, c_976])).
% 7.93/2.94  tff(c_1583, plain, (![A_126]: (r1_xboole_0('#skF_4', A_126) | ~r1_tarski(A_126, '#skF_5'))), inference(resolution, [status(thm)], [c_1540, c_1023])).
% 7.93/2.94  tff(c_1606, plain, (![A_126]: (k3_xboole_0('#skF_4', A_126)=k1_xboole_0 | ~r1_tarski(A_126, '#skF_5'))), inference(resolution, [status(thm)], [c_1583, c_6])).
% 7.93/2.94  tff(c_14206, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_3')))=k1_xboole_0), inference(resolution, [status(thm)], [c_14179, c_1606])).
% 7.93/2.94  tff(c_14250, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_2, c_14206])).
% 7.93/2.94  tff(c_14252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_371, c_14250])).
% 7.93/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.93/2.94  
% 7.93/2.94  Inference rules
% 7.93/2.94  ----------------------
% 7.93/2.94  #Ref     : 0
% 7.93/2.94  #Sup     : 3419
% 7.93/2.94  #Fact    : 0
% 7.93/2.94  #Define  : 0
% 7.93/2.94  #Split   : 8
% 7.93/2.94  #Chain   : 0
% 7.93/2.94  #Close   : 0
% 7.93/2.94  
% 7.93/2.94  Ordering : KBO
% 7.93/2.94  
% 7.93/2.94  Simplification rules
% 7.93/2.94  ----------------------
% 7.93/2.94  #Subsume      : 415
% 7.93/2.94  #Demod        : 3192
% 7.93/2.94  #Tautology    : 1947
% 7.93/2.94  #SimpNegUnit  : 91
% 7.93/2.94  #BackRed      : 8
% 7.93/2.94  
% 7.93/2.94  #Partial instantiations: 0
% 7.93/2.94  #Strategies tried      : 1
% 7.93/2.94  
% 7.93/2.94  Timing (in seconds)
% 7.93/2.94  ----------------------
% 7.93/2.94  Preprocessing        : 0.32
% 7.93/2.94  Parsing              : 0.18
% 7.93/2.94  CNF conversion       : 0.02
% 7.93/2.94  Main loop            : 1.81
% 7.93/2.94  Inferencing          : 0.40
% 7.93/2.94  Reduction            : 0.97
% 7.93/2.94  Demodulation         : 0.82
% 7.93/2.94  BG Simplification    : 0.05
% 7.93/2.94  Subsumption          : 0.29
% 7.93/2.94  Abstraction          : 0.06
% 7.93/2.94  MUC search           : 0.00
% 7.93/2.94  Cooper               : 0.00
% 7.93/2.94  Total                : 2.17
% 7.93/2.94  Index Insertion      : 0.00
% 7.93/2.94  Index Deletion       : 0.00
% 7.93/2.94  Index Matching       : 0.00
% 7.93/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
