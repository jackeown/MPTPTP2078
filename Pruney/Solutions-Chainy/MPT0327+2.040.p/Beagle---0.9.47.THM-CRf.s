%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:35 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :  101 (1159 expanded)
%              Number of leaves         :   33 ( 404 expanded)
%              Depth                    :   18
%              Number of atoms          :   97 (1487 expanded)
%              Number of equality atoms :   72 ( 995 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_50,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_166,plain,(
    ! [A_55] : k3_xboole_0(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_148])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_175,plain,(
    ! [A_55] : k3_xboole_0(A_55,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_397,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_406,plain,(
    ! [A_55] : k5_xboole_0(A_55,k1_xboole_0) = k4_xboole_0(A_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_397])).

tff(c_421,plain,(
    ! [A_55] : k5_xboole_0(A_55,k1_xboole_0) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_406])).

tff(c_625,plain,(
    ! [A_95,B_96] : k5_xboole_0(k5_xboole_0(A_95,B_96),k3_xboole_0(A_95,B_96)) = k2_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_652,plain,(
    ! [A_55] : k5_xboole_0(k5_xboole_0(A_55,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_625])).

tff(c_671,plain,(
    ! [A_55] : k2_xboole_0(A_55,k1_xboole_0) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_421,c_652])).

tff(c_338,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tarski(A_69),B_70)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_970,plain,(
    ! [A_113,B_114] :
      ( k4_xboole_0(k1_tarski(A_113),B_114) = k1_xboole_0
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_338,c_12])).

tff(c_20,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_988,plain,(
    ! [B_114,A_113] :
      ( k2_xboole_0(B_114,k1_tarski(A_113)) = k2_xboole_0(B_114,k1_xboole_0)
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_20])).

tff(c_1016,plain,(
    ! [B_114,A_113] :
      ( k2_xboole_0(B_114,k1_tarski(A_113)) = B_114
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_988])).

tff(c_415,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_397])).

tff(c_713,plain,(
    ! [A_100,B_101,C_102] : k5_xboole_0(k5_xboole_0(A_100,B_101),C_102) = k5_xboole_0(A_100,k5_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_726,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k5_xboole_0(B_101,k3_xboole_0(A_100,B_101))) = k2_xboole_0(A_100,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_32])).

tff(c_785,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k4_xboole_0(B_101,A_100)) = k2_xboole_0(A_100,B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_726])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_197,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_204,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_436,plain,(
    ! [A_80,B_81] : k2_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_448,plain,(
    ! [B_4] : k2_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_436])).

tff(c_674,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_448])).

tff(c_155,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_148])).

tff(c_412,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_397])).

tff(c_423,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_412])).

tff(c_658,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_625])).

tff(c_672,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_658])).

tff(c_793,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_672])).

tff(c_771,plain,(
    ! [B_4,C_102] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_102)) = k5_xboole_0(k1_xboole_0,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_713])).

tff(c_1140,plain,(
    ! [B_119,C_120] : k5_xboole_0(B_119,k5_xboole_0(B_119,C_120)) = C_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_771])).

tff(c_2227,plain,(
    ! [A_145,B_146] : k5_xboole_0(A_145,k2_xboole_0(A_145,B_146)) = k4_xboole_0(B_146,A_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_1140])).

tff(c_738,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k5_xboole_0(B_101,k5_xboole_0(A_100,B_101))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_423])).

tff(c_1180,plain,(
    ! [B_101,A_100] : k5_xboole_0(B_101,k5_xboole_0(A_100,B_101)) = k5_xboole_0(A_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_1140])).

tff(c_1227,plain,(
    ! [B_101,A_100] : k5_xboole_0(B_101,k5_xboole_0(A_100,B_101)) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_1180])).

tff(c_2474,plain,(
    ! [A_151,B_152] : k5_xboole_0(k2_xboole_0(A_151,B_152),k4_xboole_0(B_152,A_151)) = A_151 ),
    inference(superposition,[status(thm),theory(equality)],[c_2227,c_1227])).

tff(c_2489,plain,(
    ! [B_152,A_151] : k5_xboole_0(k4_xboole_0(B_152,A_151),A_151) = k2_xboole_0(A_151,B_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_2474,c_1227])).

tff(c_2297,plain,(
    ! [A_147,B_148] : k5_xboole_0(A_147,k4_xboole_0(A_147,B_148)) = k3_xboole_0(B_148,A_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_1140])).

tff(c_1292,plain,(
    ! [B_123,A_124] : k5_xboole_0(B_123,k5_xboole_0(A_124,B_123)) = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_1180])).

tff(c_1295,plain,(
    ! [A_124,B_123] : k5_xboole_0(k5_xboole_0(A_124,B_123),A_124) = B_123 ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_1227])).

tff(c_2312,plain,(
    ! [B_148,A_147] : k5_xboole_0(k3_xboole_0(B_148,A_147),A_147) = k4_xboole_0(A_147,B_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_1295])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3623,plain,(
    ! [A_177,B_178,C_179] : k5_xboole_0(A_177,k5_xboole_0(k3_xboole_0(A_177,B_178),C_179)) = k5_xboole_0(k4_xboole_0(A_177,B_178),C_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_713])).

tff(c_3676,plain,(
    ! [B_148,A_147] : k5_xboole_0(k4_xboole_0(B_148,A_147),A_147) = k5_xboole_0(B_148,k4_xboole_0(A_147,B_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2312,c_3623])).

tff(c_3774,plain,(
    ! [B_148,A_147] : k2_xboole_0(B_148,A_147) = k2_xboole_0(A_147,B_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2489,c_785,c_3676])).

tff(c_1139,plain,(
    ! [B_4,C_102] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_102)) = C_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_771])).

tff(c_1301,plain,(
    ! [B_123,A_124] : k5_xboole_0(B_123,A_124) = k5_xboole_0(A_124,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_1139])).

tff(c_24,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_256,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = A_61
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_270,plain,(
    ! [A_15,B_16] : k4_xboole_0(k4_xboole_0(A_15,B_16),B_16) = k4_xboole_0(A_15,B_16) ),
    inference(resolution,[status(thm)],[c_24,c_256])).

tff(c_1761,plain,(
    ! [A_133,B_134] : k5_xboole_0(A_133,k4_xboole_0(A_133,B_134)) = k3_xboole_0(A_133,B_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1140])).

tff(c_1815,plain,(
    ! [A_15,B_16] : k5_xboole_0(k4_xboole_0(A_15,B_16),k4_xboole_0(A_15,B_16)) = k3_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_1761])).

tff(c_1833,plain,(
    ! [B_16,A_15] : k3_xboole_0(B_16,k4_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_2,c_1815])).

tff(c_2075,plain,(
    ! [B_143,A_144] : k5_xboole_0(k5_xboole_0(B_143,A_144),k3_xboole_0(A_144,B_143)) = k2_xboole_0(B_143,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_625])).

tff(c_2124,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_15,B_16),B_16),k1_xboole_0) = k2_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_1833,c_2075])).

tff(c_2208,plain,(
    ! [A_15,B_16] : k2_xboole_0(k4_xboole_0(A_15,B_16),B_16) = k2_xboole_0(B_16,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_421,c_1301,c_2124])).

tff(c_48,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3554,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_48])).

tff(c_3786,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3774,c_3554])).

tff(c_3914,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_3786])).

tff(c_3918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:59:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.91  
% 4.33/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.91  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.33/1.91  
% 4.33/1.91  %Foreground sorts:
% 4.33/1.91  
% 4.33/1.91  
% 4.33/1.91  %Background operators:
% 4.33/1.91  
% 4.33/1.91  
% 4.33/1.91  %Foreground operators:
% 4.33/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.33/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.33/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.33/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.33/1.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.33/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.33/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.33/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.33/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.33/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.33/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.33/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.33/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.33/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.33/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.33/1.91  
% 4.33/1.93  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 4.33/1.93  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.33/1.93  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.33/1.93  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.33/1.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.33/1.93  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.33/1.93  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.33/1.93  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.33/1.93  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.33/1.93  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.33/1.93  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.33/1.93  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.33/1.93  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.33/1.93  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.33/1.93  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/1.93  tff(c_22, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.33/1.93  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.33/1.93  tff(c_148, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/1.93  tff(c_166, plain, (![A_55]: (k3_xboole_0(k1_xboole_0, A_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_148])).
% 4.33/1.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.33/1.93  tff(c_175, plain, (![A_55]: (k3_xboole_0(A_55, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 4.33/1.93  tff(c_397, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.33/1.93  tff(c_406, plain, (![A_55]: (k5_xboole_0(A_55, k1_xboole_0)=k4_xboole_0(A_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_175, c_397])).
% 4.33/1.93  tff(c_421, plain, (![A_55]: (k5_xboole_0(A_55, k1_xboole_0)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_406])).
% 4.33/1.93  tff(c_625, plain, (![A_95, B_96]: (k5_xboole_0(k5_xboole_0(A_95, B_96), k3_xboole_0(A_95, B_96))=k2_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.33/1.93  tff(c_652, plain, (![A_55]: (k5_xboole_0(k5_xboole_0(A_55, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_175, c_625])).
% 4.33/1.93  tff(c_671, plain, (![A_55]: (k2_xboole_0(A_55, k1_xboole_0)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_421, c_652])).
% 4.33/1.93  tff(c_338, plain, (![A_69, B_70]: (r1_tarski(k1_tarski(A_69), B_70) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.33/1.93  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.33/1.93  tff(c_970, plain, (![A_113, B_114]: (k4_xboole_0(k1_tarski(A_113), B_114)=k1_xboole_0 | ~r2_hidden(A_113, B_114))), inference(resolution, [status(thm)], [c_338, c_12])).
% 4.33/1.93  tff(c_20, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.33/1.93  tff(c_988, plain, (![B_114, A_113]: (k2_xboole_0(B_114, k1_tarski(A_113))=k2_xboole_0(B_114, k1_xboole_0) | ~r2_hidden(A_113, B_114))), inference(superposition, [status(thm), theory('equality')], [c_970, c_20])).
% 4.33/1.93  tff(c_1016, plain, (![B_114, A_113]: (k2_xboole_0(B_114, k1_tarski(A_113))=B_114 | ~r2_hidden(A_113, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_671, c_988])).
% 4.33/1.93  tff(c_415, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_397])).
% 4.33/1.93  tff(c_713, plain, (![A_100, B_101, C_102]: (k5_xboole_0(k5_xboole_0(A_100, B_101), C_102)=k5_xboole_0(A_100, k5_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.33/1.93  tff(c_32, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.33/1.93  tff(c_726, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k5_xboole_0(B_101, k3_xboole_0(A_100, B_101)))=k2_xboole_0(A_100, B_101))), inference(superposition, [status(thm), theory('equality')], [c_713, c_32])).
% 4.33/1.93  tff(c_785, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k4_xboole_0(B_101, A_100))=k2_xboole_0(A_100, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_726])).
% 4.33/1.93  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.33/1.93  tff(c_197, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.33/1.93  tff(c_204, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_197])).
% 4.33/1.93  tff(c_436, plain, (![A_80, B_81]: (k2_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.33/1.93  tff(c_448, plain, (![B_4]: (k2_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_204, c_436])).
% 4.33/1.93  tff(c_674, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_671, c_448])).
% 4.33/1.93  tff(c_155, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_148])).
% 4.33/1.93  tff(c_412, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_155, c_397])).
% 4.33/1.93  tff(c_423, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_204, c_412])).
% 4.33/1.93  tff(c_658, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_155, c_625])).
% 4.33/1.93  tff(c_672, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_658])).
% 4.33/1.93  tff(c_793, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_674, c_672])).
% 4.33/1.93  tff(c_771, plain, (![B_4, C_102]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_102))=k5_xboole_0(k1_xboole_0, C_102))), inference(superposition, [status(thm), theory('equality')], [c_423, c_713])).
% 4.33/1.93  tff(c_1140, plain, (![B_119, C_120]: (k5_xboole_0(B_119, k5_xboole_0(B_119, C_120))=C_120)), inference(demodulation, [status(thm), theory('equality')], [c_793, c_771])).
% 4.33/1.93  tff(c_2227, plain, (![A_145, B_146]: (k5_xboole_0(A_145, k2_xboole_0(A_145, B_146))=k4_xboole_0(B_146, A_145))), inference(superposition, [status(thm), theory('equality')], [c_785, c_1140])).
% 4.33/1.93  tff(c_738, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k5_xboole_0(B_101, k5_xboole_0(A_100, B_101)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_713, c_423])).
% 4.33/1.93  tff(c_1180, plain, (![B_101, A_100]: (k5_xboole_0(B_101, k5_xboole_0(A_100, B_101))=k5_xboole_0(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_738, c_1140])).
% 4.33/1.93  tff(c_1227, plain, (![B_101, A_100]: (k5_xboole_0(B_101, k5_xboole_0(A_100, B_101))=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_1180])).
% 4.33/1.93  tff(c_2474, plain, (![A_151, B_152]: (k5_xboole_0(k2_xboole_0(A_151, B_152), k4_xboole_0(B_152, A_151))=A_151)), inference(superposition, [status(thm), theory('equality')], [c_2227, c_1227])).
% 4.33/1.93  tff(c_2489, plain, (![B_152, A_151]: (k5_xboole_0(k4_xboole_0(B_152, A_151), A_151)=k2_xboole_0(A_151, B_152))), inference(superposition, [status(thm), theory('equality')], [c_2474, c_1227])).
% 4.33/1.93  tff(c_2297, plain, (![A_147, B_148]: (k5_xboole_0(A_147, k4_xboole_0(A_147, B_148))=k3_xboole_0(B_148, A_147))), inference(superposition, [status(thm), theory('equality')], [c_415, c_1140])).
% 4.33/1.93  tff(c_1292, plain, (![B_123, A_124]: (k5_xboole_0(B_123, k5_xboole_0(A_124, B_123))=A_124)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_1180])).
% 4.33/1.93  tff(c_1295, plain, (![A_124, B_123]: (k5_xboole_0(k5_xboole_0(A_124, B_123), A_124)=B_123)), inference(superposition, [status(thm), theory('equality')], [c_1292, c_1227])).
% 4.33/1.93  tff(c_2312, plain, (![B_148, A_147]: (k5_xboole_0(k3_xboole_0(B_148, A_147), A_147)=k4_xboole_0(A_147, B_148))), inference(superposition, [status(thm), theory('equality')], [c_2297, c_1295])).
% 4.33/1.93  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.33/1.93  tff(c_3623, plain, (![A_177, B_178, C_179]: (k5_xboole_0(A_177, k5_xboole_0(k3_xboole_0(A_177, B_178), C_179))=k5_xboole_0(k4_xboole_0(A_177, B_178), C_179))), inference(superposition, [status(thm), theory('equality')], [c_14, c_713])).
% 4.33/1.93  tff(c_3676, plain, (![B_148, A_147]: (k5_xboole_0(k4_xboole_0(B_148, A_147), A_147)=k5_xboole_0(B_148, k4_xboole_0(A_147, B_148)))), inference(superposition, [status(thm), theory('equality')], [c_2312, c_3623])).
% 4.33/1.93  tff(c_3774, plain, (![B_148, A_147]: (k2_xboole_0(B_148, A_147)=k2_xboole_0(A_147, B_148))), inference(demodulation, [status(thm), theory('equality')], [c_2489, c_785, c_3676])).
% 4.33/1.93  tff(c_1139, plain, (![B_4, C_102]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_102))=C_102)), inference(demodulation, [status(thm), theory('equality')], [c_793, c_771])).
% 4.33/1.93  tff(c_1301, plain, (![B_123, A_124]: (k5_xboole_0(B_123, A_124)=k5_xboole_0(A_124, B_123))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_1139])).
% 4.33/1.93  tff(c_24, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.33/1.93  tff(c_256, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=A_61 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.33/1.93  tff(c_270, plain, (![A_15, B_16]: (k4_xboole_0(k4_xboole_0(A_15, B_16), B_16)=k4_xboole_0(A_15, B_16))), inference(resolution, [status(thm)], [c_24, c_256])).
% 4.33/1.93  tff(c_1761, plain, (![A_133, B_134]: (k5_xboole_0(A_133, k4_xboole_0(A_133, B_134))=k3_xboole_0(A_133, B_134))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1140])).
% 4.33/1.93  tff(c_1815, plain, (![A_15, B_16]: (k5_xboole_0(k4_xboole_0(A_15, B_16), k4_xboole_0(A_15, B_16))=k3_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(superposition, [status(thm), theory('equality')], [c_270, c_1761])).
% 4.33/1.93  tff(c_1833, plain, (![B_16, A_15]: (k3_xboole_0(B_16, k4_xboole_0(A_15, B_16))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_423, c_2, c_1815])).
% 4.33/1.93  tff(c_2075, plain, (![B_143, A_144]: (k5_xboole_0(k5_xboole_0(B_143, A_144), k3_xboole_0(A_144, B_143))=k2_xboole_0(B_143, A_144))), inference(superposition, [status(thm), theory('equality')], [c_2, c_625])).
% 4.33/1.93  tff(c_2124, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_15, B_16), B_16), k1_xboole_0)=k2_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(superposition, [status(thm), theory('equality')], [c_1833, c_2075])).
% 4.33/1.93  tff(c_2208, plain, (![A_15, B_16]: (k2_xboole_0(k4_xboole_0(A_15, B_16), B_16)=k2_xboole_0(B_16, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_785, c_421, c_1301, c_2124])).
% 4.33/1.93  tff(c_48, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/1.93  tff(c_3554, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2208, c_48])).
% 4.33/1.93  tff(c_3786, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3774, c_3554])).
% 4.33/1.93  tff(c_3914, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1016, c_3786])).
% 4.33/1.93  tff(c_3918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3914])).
% 4.33/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.93  
% 4.33/1.93  Inference rules
% 4.33/1.93  ----------------------
% 4.33/1.93  #Ref     : 0
% 4.33/1.93  #Sup     : 943
% 4.33/1.93  #Fact    : 0
% 4.33/1.93  #Define  : 0
% 4.33/1.93  #Split   : 1
% 4.33/1.93  #Chain   : 0
% 4.33/1.93  #Close   : 0
% 4.33/1.93  
% 4.33/1.93  Ordering : KBO
% 4.33/1.93  
% 4.33/1.93  Simplification rules
% 4.33/1.93  ----------------------
% 4.33/1.93  #Subsume      : 35
% 4.33/1.93  #Demod        : 777
% 4.33/1.93  #Tautology    : 634
% 4.33/1.93  #SimpNegUnit  : 0
% 4.33/1.93  #BackRed      : 6
% 4.33/1.93  
% 4.33/1.93  #Partial instantiations: 0
% 4.33/1.93  #Strategies tried      : 1
% 4.33/1.93  
% 4.33/1.93  Timing (in seconds)
% 4.33/1.93  ----------------------
% 4.33/1.93  Preprocessing        : 0.31
% 4.33/1.93  Parsing              : 0.16
% 4.33/1.93  CNF conversion       : 0.02
% 4.33/1.93  Main loop            : 0.83
% 4.33/1.93  Inferencing          : 0.28
% 4.33/1.93  Reduction            : 0.35
% 4.33/1.93  Demodulation         : 0.28
% 4.33/1.93  BG Simplification    : 0.03
% 4.33/1.93  Subsumption          : 0.11
% 4.33/1.93  Abstraction          : 0.05
% 4.33/1.93  MUC search           : 0.00
% 4.33/1.93  Cooper               : 0.00
% 4.33/1.93  Total                : 1.19
% 4.33/1.93  Index Insertion      : 0.00
% 4.33/1.93  Index Deletion       : 0.00
% 4.33/1.94  Index Matching       : 0.00
% 4.33/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
