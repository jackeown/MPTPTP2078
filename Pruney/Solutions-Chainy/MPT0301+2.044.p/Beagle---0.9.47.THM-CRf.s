%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:46 EST 2020

% Result     : Theorem 10.77s
% Output     : CNFRefutation 10.94s
% Verified   : 
% Statistics : Number of formulae       :  275 (1143 expanded)
%              Number of leaves         :   29 ( 375 expanded)
%              Depth                    :   12
%              Number of atoms          :  411 (2217 expanded)
%              Number of equality atoms :  153 ( 947 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E] :
      ~ ( r2_hidden(A,k3_xboole_0(k2_zfmisc_1(B,C),k2_zfmisc_1(D,E)))
        & ! [F,G] :
            ~ ( A = k4_tarski(F,G)
              & r2_hidden(F,k3_xboole_0(B,D))
              & r2_hidden(G,k3_xboole_0(C,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_728,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ r2_hidden('#skF_2'(A_115,B_116,C_117),C_117)
      | r2_hidden('#skF_3'(A_115,B_116,C_117),C_117)
      | k4_xboole_0(A_115,B_116) = C_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_737,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k4_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_728])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_6','#skF_7') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_75,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_416,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( r2_hidden(k4_tarski(A_92,B_93),k2_zfmisc_1(C_94,D_95))
      | ~ r2_hidden(B_93,D_95)
      | ~ r2_hidden(A_92,C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_429,plain,(
    ! [A_92,B_93] :
      ( r2_hidden(k4_tarski(A_92,B_93),k1_xboole_0)
      | ~ r2_hidden(B_93,'#skF_9')
      | ~ r2_hidden(A_92,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_416])).

tff(c_606,plain,(
    ! [A_107,B_108] :
      ( r2_hidden(k4_tarski(A_107,B_108),k1_xboole_0)
      | ~ r2_hidden(B_108,'#skF_9')
      | ~ r2_hidden(A_107,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_416])).

tff(c_36,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_129,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_56] : r1_tarski(A_56,A_56) ),
    inference(resolution,[status(thm)],[c_129,c_4])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_153,plain,(
    ! [A_57] : k3_xboole_0(A_57,A_57) = A_57 ),
    inference(resolution,[status(thm)],[c_145,c_34])).

tff(c_30,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_159,plain,(
    ! [A_57] : k5_xboole_0(A_57,A_57) = k4_xboole_0(A_57,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_30])).

tff(c_208,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_159])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_213,plain,(
    ! [D_11,A_67] :
      ( ~ r2_hidden(D_11,A_67)
      | ~ r2_hidden(D_11,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_10])).

tff(c_829,plain,(
    ! [A_122,B_123] :
      ( ~ r2_hidden(k4_tarski(A_122,B_123),k1_xboole_0)
      | ~ r2_hidden(B_123,'#skF_9')
      | ~ r2_hidden(A_122,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_606,c_213])).

tff(c_833,plain,(
    ! [B_93,A_92] :
      ( ~ r2_hidden(B_93,'#skF_9')
      | ~ r2_hidden(A_92,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_429,c_829])).

tff(c_836,plain,(
    ! [A_124] : ~ r2_hidden(A_124,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_833])).

tff(c_859,plain,(
    ! [B_126] : k4_xboole_0('#skF_8',B_126) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_737,c_836])).

tff(c_167,plain,(
    ! [A_57] : k4_xboole_0(A_57,A_57) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_159])).

tff(c_876,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_167])).

tff(c_891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_876])).

tff(c_894,plain,(
    ! [B_127] : ~ r2_hidden(B_127,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_927,plain,(
    ! [B_132] : k4_xboole_0('#skF_9',B_132) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_737,c_894])).

tff(c_944,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_167])).

tff(c_959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_944])).

tff(c_960,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_962,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_960])).

tff(c_966,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_36])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1033,plain,(
    ! [A_145,B_146] :
      ( ~ r2_hidden('#skF_1'(A_145,B_146),B_146)
      | r1_tarski(A_145,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1045,plain,(
    ! [A_150] : r1_tarski(A_150,A_150) ),
    inference(resolution,[status(thm)],[c_6,c_1033])).

tff(c_1053,plain,(
    ! [A_151] : k3_xboole_0(A_151,A_151) = A_151 ),
    inference(resolution,[status(thm)],[c_1045,c_34])).

tff(c_1059,plain,(
    ! [A_151] : k5_xboole_0(A_151,A_151) = k4_xboole_0(A_151,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_30])).

tff(c_1067,plain,(
    ! [A_151] : k4_xboole_0(A_151,A_151) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_1059])).

tff(c_1075,plain,(
    ! [D_153,A_154,B_155] :
      ( r2_hidden(D_153,A_154)
      | ~ r2_hidden(D_153,k4_xboole_0(A_154,B_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2102,plain,(
    ! [A_262,B_263,B_264] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_262,B_263),B_264),A_262)
      | r1_tarski(k4_xboole_0(A_262,B_263),B_264) ) ),
    inference(resolution,[status(thm)],[c_6,c_1075])).

tff(c_2157,plain,(
    ! [A_265,B_266] : r1_tarski(k4_xboole_0(A_265,B_266),A_265) ),
    inference(resolution,[status(thm)],[c_2102,c_4])).

tff(c_2230,plain,(
    ! [A_272,B_273] : k3_xboole_0(k4_xboole_0(A_272,B_273),A_272) = k4_xboole_0(A_272,B_273) ),
    inference(resolution,[status(thm)],[c_2157,c_34])).

tff(c_2261,plain,(
    ! [A_272,B_273] : k5_xboole_0(k4_xboole_0(A_272,B_273),k4_xboole_0(A_272,B_273)) = k4_xboole_0(k4_xboole_0(A_272,B_273),A_272) ),
    inference(superposition,[status(thm),theory(equality)],[c_2230,c_30])).

tff(c_2284,plain,(
    ! [A_272,B_273] : k4_xboole_0(k4_xboole_0(A_272,B_273),A_272) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_2261])).

tff(c_1432,plain,(
    ! [A_195,B_196,C_197] :
      ( r2_hidden('#skF_2'(A_195,B_196,C_197),A_195)
      | r2_hidden('#skF_3'(A_195,B_196,C_197),C_197)
      | k4_xboole_0(A_195,B_196) = C_197 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5314,plain,(
    ! [A_405,B_406,B_407,C_408] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_405,B_406),B_407,C_408),A_405)
      | r2_hidden('#skF_3'(k4_xboole_0(A_405,B_406),B_407,C_408),C_408)
      | k4_xboole_0(k4_xboole_0(A_405,B_406),B_407) = C_408 ) ),
    inference(resolution,[status(thm)],[c_1432,c_12])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5347,plain,(
    ! [A_405,B_406,C_408] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_405,B_406),A_405,C_408),C_408)
      | k4_xboole_0(k4_xboole_0(A_405,B_406),A_405) = C_408 ) ),
    inference(resolution,[status(thm)],[c_5314,c_22])).

tff(c_5484,plain,(
    ! [A_409,B_410,C_411] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_409,B_410),A_409,C_411),C_411)
      | C_411 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2284,c_5347])).

tff(c_5542,plain,(
    ! [A_151,C_411] :
      ( r2_hidden('#skF_3'('#skF_7',A_151,C_411),C_411)
      | C_411 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_5484])).

tff(c_1049,plain,(
    ! [A_150] : k3_xboole_0(A_150,A_150) = A_150 ),
    inference(resolution,[status(thm)],[c_1045,c_34])).

tff(c_1725,plain,(
    ! [A_218,B_221,E_222,D_219,C_220] :
      ( r2_hidden('#skF_5'(A_218,D_219,C_220,B_221,E_222),k3_xboole_0(C_220,E_222))
      | ~ r2_hidden(A_218,k3_xboole_0(k2_zfmisc_1(B_221,C_220),k2_zfmisc_1(D_219,E_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1740,plain,(
    ! [A_218,B_221,C_220] :
      ( r2_hidden('#skF_5'(A_218,B_221,C_220,B_221,C_220),k3_xboole_0(C_220,C_220))
      | ~ r2_hidden(A_218,k2_zfmisc_1(B_221,C_220)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_1725])).

tff(c_4443,plain,(
    ! [A_379,B_380,C_381] :
      ( r2_hidden('#skF_5'(A_379,B_380,C_381,B_380,C_381),C_381)
      | ~ r2_hidden(A_379,k2_zfmisc_1(B_380,C_381)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1740])).

tff(c_1106,plain,(
    ! [A_157] : k4_xboole_0(A_157,A_157) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_1059])).

tff(c_1111,plain,(
    ! [D_11,A_157] :
      ( r2_hidden(D_11,A_157)
      | ~ r2_hidden(D_11,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_12])).

tff(c_4488,plain,(
    ! [A_379,B_380,A_157] :
      ( r2_hidden('#skF_5'(A_379,B_380,'#skF_7',B_380,'#skF_7'),A_157)
      | ~ r2_hidden(A_379,k2_zfmisc_1(B_380,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4443,c_1111])).

tff(c_6186,plain,(
    ! [A_438,B_439,A_440] :
      ( r2_hidden('#skF_5'(A_438,B_439,'#skF_7',B_439,'#skF_7'),A_440)
      | ~ r2_hidden(A_438,k2_zfmisc_1(B_439,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4443,c_1111])).

tff(c_7477,plain,(
    ! [A_490,B_491,B_492] :
      ( ~ r2_hidden('#skF_5'(A_490,B_491,'#skF_7',B_491,'#skF_7'),B_492)
      | ~ r2_hidden(A_490,k2_zfmisc_1(B_491,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_6186,c_10])).

tff(c_7497,plain,(
    ! [A_493,B_494] : ~ r2_hidden(A_493,k2_zfmisc_1(B_494,'#skF_7')) ),
    inference(resolution,[status(thm)],[c_4488,c_7477])).

tff(c_7663,plain,(
    ! [B_494] : k2_zfmisc_1(B_494,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5542,c_7497])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_6','#skF_7') != k1_xboole_0
    | k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_963,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_971,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_963])).

tff(c_7694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7663,c_971])).

tff(c_7695,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7704,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_7695])).

tff(c_961,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_7725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7704,c_962,c_961])).

tff(c_7726,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_7731,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7726,c_36])).

tff(c_7800,plain,(
    ! [A_511,B_512] :
      ( r2_hidden('#skF_1'(A_511,B_512),A_511)
      | r1_tarski(A_511,B_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7811,plain,(
    ! [A_513] : r1_tarski(A_513,A_513) ),
    inference(resolution,[status(thm)],[c_7800,c_4])).

tff(c_7819,plain,(
    ! [A_514] : k3_xboole_0(A_514,A_514) = A_514 ),
    inference(resolution,[status(thm)],[c_7811,c_34])).

tff(c_7825,plain,(
    ! [A_514] : k5_xboole_0(A_514,A_514) = k4_xboole_0(A_514,A_514) ),
    inference(superposition,[status(thm),theory(equality)],[c_7819,c_30])).

tff(c_7833,plain,(
    ! [A_514] : k4_xboole_0(A_514,A_514) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7731,c_7825])).

tff(c_7836,plain,(
    ! [D_515,A_516,B_517] :
      ( r2_hidden(D_515,A_516)
      | ~ r2_hidden(D_515,k4_xboole_0(A_516,B_517)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8874,plain,(
    ! [A_626,B_627,B_628] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_626,B_627),B_628),A_626)
      | r1_tarski(k4_xboole_0(A_626,B_627),B_628) ) ),
    inference(resolution,[status(thm)],[c_6,c_7836])).

tff(c_8929,plain,(
    ! [A_629,B_630] : r1_tarski(k4_xboole_0(A_629,B_630),A_629) ),
    inference(resolution,[status(thm)],[c_8874,c_4])).

tff(c_9002,plain,(
    ! [A_636,B_637] : k3_xboole_0(k4_xboole_0(A_636,B_637),A_636) = k4_xboole_0(A_636,B_637) ),
    inference(resolution,[status(thm)],[c_8929,c_34])).

tff(c_9033,plain,(
    ! [A_636,B_637] : k5_xboole_0(k4_xboole_0(A_636,B_637),k4_xboole_0(A_636,B_637)) = k4_xboole_0(k4_xboole_0(A_636,B_637),A_636) ),
    inference(superposition,[status(thm),theory(equality)],[c_9002,c_30])).

tff(c_9056,plain,(
    ! [A_636,B_637] : k4_xboole_0(k4_xboole_0(A_636,B_637),A_636) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7731,c_9033])).

tff(c_8198,plain,(
    ! [A_557,B_558,C_559] :
      ( r2_hidden('#skF_2'(A_557,B_558,C_559),A_557)
      | r2_hidden('#skF_3'(A_557,B_558,C_559),C_559)
      | k4_xboole_0(A_557,B_558) = C_559 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13040,plain,(
    ! [A_811,B_812,B_813,C_814] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_811,B_812),B_813,C_814),A_811)
      | r2_hidden('#skF_3'(k4_xboole_0(A_811,B_812),B_813,C_814),C_814)
      | k4_xboole_0(k4_xboole_0(A_811,B_812),B_813) = C_814 ) ),
    inference(resolution,[status(thm)],[c_8198,c_12])).

tff(c_13073,plain,(
    ! [A_811,B_812,C_814] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_811,B_812),A_811,C_814),C_814)
      | k4_xboole_0(k4_xboole_0(A_811,B_812),A_811) = C_814 ) ),
    inference(resolution,[status(thm)],[c_13040,c_22])).

tff(c_13215,plain,(
    ! [A_815,B_816,C_817] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_815,B_816),A_815,C_817),C_817)
      | C_817 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9056,c_13073])).

tff(c_13273,plain,(
    ! [A_514,C_817] :
      ( r2_hidden('#skF_3'('#skF_6',A_514,C_817),C_817)
      | C_817 = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7833,c_13215])).

tff(c_7815,plain,(
    ! [A_513] : k3_xboole_0(A_513,A_513) = A_513 ),
    inference(resolution,[status(thm)],[c_7811,c_34])).

tff(c_8497,plain,(
    ! [C_584,B_585,E_586,D_583,A_582] :
      ( r2_hidden('#skF_4'(A_582,D_583,C_584,B_585,E_586),k3_xboole_0(B_585,D_583))
      | ~ r2_hidden(A_582,k3_xboole_0(k2_zfmisc_1(B_585,C_584),k2_zfmisc_1(D_583,E_586))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8512,plain,(
    ! [A_582,B_585,C_584] :
      ( r2_hidden('#skF_4'(A_582,B_585,C_584,B_585,C_584),k3_xboole_0(B_585,B_585))
      | ~ r2_hidden(A_582,k2_zfmisc_1(B_585,C_584)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7815,c_8497])).

tff(c_11923,plain,(
    ! [A_762,B_763,C_764] :
      ( r2_hidden('#skF_4'(A_762,B_763,C_764,B_763,C_764),B_763)
      | ~ r2_hidden(A_762,k2_zfmisc_1(B_763,C_764)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7815,c_8512])).

tff(c_7871,plain,(
    ! [A_520] : k4_xboole_0(A_520,A_520) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7731,c_7825])).

tff(c_7876,plain,(
    ! [D_11,A_520] :
      ( r2_hidden(D_11,A_520)
      | ~ r2_hidden(D_11,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7871,c_12])).

tff(c_11968,plain,(
    ! [A_762,C_764,A_520] :
      ( r2_hidden('#skF_4'(A_762,'#skF_6',C_764,'#skF_6',C_764),A_520)
      | ~ r2_hidden(A_762,k2_zfmisc_1('#skF_6',C_764)) ) ),
    inference(resolution,[status(thm)],[c_11923,c_7876])).

tff(c_8540,plain,(
    ! [D_590,A_589,E_593,C_591,B_592] :
      ( r2_hidden('#skF_5'(A_589,D_590,C_591,B_592,E_593),k3_xboole_0(C_591,E_593))
      | ~ r2_hidden(A_589,k3_xboole_0(k2_zfmisc_1(B_592,C_591),k2_zfmisc_1(D_590,E_593))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8555,plain,(
    ! [A_589,B_592,C_591] :
      ( r2_hidden('#skF_5'(A_589,B_592,C_591,B_592,C_591),k3_xboole_0(C_591,C_591))
      | ~ r2_hidden(A_589,k2_zfmisc_1(B_592,C_591)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7815,c_8540])).

tff(c_11874,plain,(
    ! [A_759,B_760,C_761] :
      ( r2_hidden('#skF_5'(A_759,B_760,C_761,B_760,C_761),C_761)
      | ~ r2_hidden(A_759,k2_zfmisc_1(B_760,C_761)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7815,c_8555])).

tff(c_11919,plain,(
    ! [A_759,B_760,A_520] :
      ( r2_hidden('#skF_5'(A_759,B_760,'#skF_6',B_760,'#skF_6'),A_520)
      | ~ r2_hidden(A_759,k2_zfmisc_1(B_760,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_11874,c_7876])).

tff(c_12460,plain,(
    ! [A_782,B_783,A_784] :
      ( r2_hidden('#skF_5'(A_782,B_783,'#skF_6',B_783,'#skF_6'),A_784)
      | ~ r2_hidden(A_782,k2_zfmisc_1(B_783,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_11874,c_7876])).

tff(c_14011,plain,(
    ! [A_848,B_849,B_850] :
      ( ~ r2_hidden('#skF_5'(A_848,B_849,'#skF_6',B_849,'#skF_6'),B_850)
      | ~ r2_hidden(A_848,k2_zfmisc_1(B_849,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_12460,c_10])).

tff(c_14031,plain,(
    ! [A_851,B_852] : ~ r2_hidden(A_851,k2_zfmisc_1(B_852,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_11919,c_14011])).

tff(c_14609,plain,(
    ! [A_859,C_860] : ~ r2_hidden(A_859,k2_zfmisc_1('#skF_6',C_860)) ),
    inference(resolution,[status(thm)],[c_11968,c_14031])).

tff(c_14777,plain,(
    ! [C_860] : k2_zfmisc_1('#skF_6',C_860) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_13273,c_14609])).

tff(c_7728,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_7737,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7726,c_7728])).

tff(c_14813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14777,c_7737])).

tff(c_14814,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_14824,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7726,c_14814])).

tff(c_14830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14824,c_7726,c_961])).

tff(c_14832,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14834,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14832,c_36])).

tff(c_21340,plain,(
    ! [A_1222,B_1223] :
      ( ~ r2_hidden('#skF_1'(A_1222,B_1223),B_1223)
      | r1_tarski(A_1222,B_1223) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21346,plain,(
    ! [A_1224] : r1_tarski(A_1224,A_1224) ),
    inference(resolution,[status(thm)],[c_6,c_21340])).

tff(c_21354,plain,(
    ! [A_1225] : k3_xboole_0(A_1225,A_1225) = A_1225 ),
    inference(resolution,[status(thm)],[c_21346,c_34])).

tff(c_21360,plain,(
    ! [A_1225] : k5_xboole_0(A_1225,A_1225) = k4_xboole_0(A_1225,A_1225) ),
    inference(superposition,[status(thm),theory(equality)],[c_21354,c_30])).

tff(c_21368,plain,(
    ! [A_1225] : k4_xboole_0(A_1225,A_1225) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14834,c_21360])).

tff(c_21313,plain,(
    ! [A_1215,B_1216] :
      ( r2_hidden('#skF_1'(A_1215,B_1216),A_1215)
      | r1_tarski(A_1215,B_1216) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22345,plain,(
    ! [A_1326,B_1327,B_1328] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_1326,B_1327),B_1328),A_1326)
      | r1_tarski(k4_xboole_0(A_1326,B_1327),B_1328) ) ),
    inference(resolution,[status(thm)],[c_21313,c_12])).

tff(c_22394,plain,(
    ! [A_1329,B_1330] : r1_tarski(k4_xboole_0(A_1329,B_1330),A_1329) ),
    inference(resolution,[status(thm)],[c_22345,c_4])).

tff(c_22462,plain,(
    ! [A_1336,B_1337] : k3_xboole_0(k4_xboole_0(A_1336,B_1337),A_1336) = k4_xboole_0(A_1336,B_1337) ),
    inference(resolution,[status(thm)],[c_22394,c_34])).

tff(c_22493,plain,(
    ! [A_1336,B_1337] : k5_xboole_0(k4_xboole_0(A_1336,B_1337),k4_xboole_0(A_1336,B_1337)) = k4_xboole_0(k4_xboole_0(A_1336,B_1337),A_1336) ),
    inference(superposition,[status(thm),theory(equality)],[c_22462,c_30])).

tff(c_22516,plain,(
    ! [A_1336,B_1337] : k4_xboole_0(k4_xboole_0(A_1336,B_1337),A_1336) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14834,c_22493])).

tff(c_21818,plain,(
    ! [A_1277,B_1278,C_1279] :
      ( r2_hidden('#skF_2'(A_1277,B_1278,C_1279),A_1277)
      | r2_hidden('#skF_3'(A_1277,B_1278,C_1279),C_1279)
      | k4_xboole_0(A_1277,B_1278) = C_1279 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_25934,plain,(
    ! [A_1492,B_1493,B_1494,C_1495] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_1492,B_1493),B_1494,C_1495),A_1492)
      | r2_hidden('#skF_3'(k4_xboole_0(A_1492,B_1493),B_1494,C_1495),C_1495)
      | k4_xboole_0(k4_xboole_0(A_1492,B_1493),B_1494) = C_1495 ) ),
    inference(resolution,[status(thm)],[c_21818,c_12])).

tff(c_25967,plain,(
    ! [A_1492,B_1493,C_1495] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_1492,B_1493),A_1492,C_1495),C_1495)
      | k4_xboole_0(k4_xboole_0(A_1492,B_1493),A_1492) = C_1495 ) ),
    inference(resolution,[status(thm)],[c_25934,c_22])).

tff(c_26109,plain,(
    ! [A_1496,B_1497,C_1498] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_1496,B_1497),A_1496,C_1498),C_1498)
      | C_1498 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22516,c_25967])).

tff(c_26167,plain,(
    ! [A_1225,C_1498] :
      ( r2_hidden('#skF_3'('#skF_9',A_1225,C_1498),C_1498)
      | C_1498 = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21368,c_26109])).

tff(c_21350,plain,(
    ! [A_1224] : k3_xboole_0(A_1224,A_1224) = A_1224 ),
    inference(resolution,[status(thm)],[c_21346,c_34])).

tff(c_22022,plain,(
    ! [B_1296,D_1294,A_1293,E_1297,C_1295] :
      ( r2_hidden('#skF_4'(A_1293,D_1294,C_1295,B_1296,E_1297),k3_xboole_0(B_1296,D_1294))
      | ~ r2_hidden(A_1293,k3_xboole_0(k2_zfmisc_1(B_1296,C_1295),k2_zfmisc_1(D_1294,E_1297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22037,plain,(
    ! [A_1293,B_1296,C_1295] :
      ( r2_hidden('#skF_4'(A_1293,B_1296,C_1295,B_1296,C_1295),k3_xboole_0(B_1296,B_1296))
      | ~ r2_hidden(A_1293,k2_zfmisc_1(B_1296,C_1295)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21350,c_22022])).

tff(c_25758,plain,(
    ! [A_1486,B_1487,C_1488] :
      ( r2_hidden('#skF_4'(A_1486,B_1487,C_1488,B_1487,C_1488),B_1487)
      | ~ r2_hidden(A_1486,k2_zfmisc_1(B_1487,C_1488)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21350,c_22037])).

tff(c_21405,plain,(
    ! [A_1231] : k4_xboole_0(A_1231,A_1231) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14834,c_21360])).

tff(c_21413,plain,(
    ! [D_11,A_1231] :
      ( r2_hidden(D_11,A_1231)
      | ~ r2_hidden(D_11,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21405,c_12])).

tff(c_25803,plain,(
    ! [A_1486,C_1488,A_1231] :
      ( r2_hidden('#skF_4'(A_1486,'#skF_9',C_1488,'#skF_9',C_1488),A_1231)
      | ~ r2_hidden(A_1486,k2_zfmisc_1('#skF_9',C_1488)) ) ),
    inference(resolution,[status(thm)],[c_25758,c_21413])).

tff(c_26972,plain,(
    ! [A_1531,C_1532,A_1533] :
      ( r2_hidden('#skF_4'(A_1531,'#skF_9',C_1532,'#skF_9',C_1532),A_1533)
      | ~ r2_hidden(A_1531,k2_zfmisc_1('#skF_9',C_1532)) ) ),
    inference(resolution,[status(thm)],[c_25758,c_21413])).

tff(c_27364,plain,(
    ! [A_1545,C_1546,B_1547] :
      ( ~ r2_hidden('#skF_4'(A_1545,'#skF_9',C_1546,'#skF_9',C_1546),B_1547)
      | ~ r2_hidden(A_1545,k2_zfmisc_1('#skF_9',C_1546)) ) ),
    inference(resolution,[status(thm)],[c_26972,c_10])).

tff(c_27404,plain,(
    ! [A_1551,C_1552] : ~ r2_hidden(A_1551,k2_zfmisc_1('#skF_9',C_1552)) ),
    inference(resolution,[status(thm)],[c_25803,c_27364])).

tff(c_27554,plain,(
    ! [C_1552] : k2_zfmisc_1('#skF_9',C_1552) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_26167,c_27404])).

tff(c_14901,plain,(
    ! [A_878,B_879] :
      ( ~ r2_hidden('#skF_1'(A_878,B_879),B_879)
      | r1_tarski(A_878,B_879) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14922,plain,(
    ! [A_882] : r1_tarski(A_882,A_882) ),
    inference(resolution,[status(thm)],[c_6,c_14901])).

tff(c_14930,plain,(
    ! [A_883] : k3_xboole_0(A_883,A_883) = A_883 ),
    inference(resolution,[status(thm)],[c_14922,c_34])).

tff(c_14936,plain,(
    ! [A_883] : k5_xboole_0(A_883,A_883) = k4_xboole_0(A_883,A_883) ),
    inference(superposition,[status(thm),theory(equality)],[c_14930,c_30])).

tff(c_14944,plain,(
    ! [A_883] : k4_xboole_0(A_883,A_883) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14834,c_14936])).

tff(c_14976,plain,(
    ! [D_886,A_887,B_888] :
      ( r2_hidden(D_886,A_887)
      | ~ r2_hidden(D_886,k4_xboole_0(A_887,B_888)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15840,plain,(
    ! [A_981,B_982,B_983] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_981,B_982),B_983),A_981)
      | r1_tarski(k4_xboole_0(A_981,B_982),B_983) ) ),
    inference(resolution,[status(thm)],[c_6,c_14976])).

tff(c_15963,plain,(
    ! [A_987,B_988] : r1_tarski(k4_xboole_0(A_987,B_988),A_987) ),
    inference(resolution,[status(thm)],[c_15840,c_4])).

tff(c_15987,plain,(
    ! [A_989,B_990] : k3_xboole_0(k4_xboole_0(A_989,B_990),A_989) = k4_xboole_0(A_989,B_990) ),
    inference(resolution,[status(thm)],[c_15963,c_34])).

tff(c_16018,plain,(
    ! [A_989,B_990] : k5_xboole_0(k4_xboole_0(A_989,B_990),k4_xboole_0(A_989,B_990)) = k4_xboole_0(k4_xboole_0(A_989,B_990),A_989) ),
    inference(superposition,[status(thm),theory(equality)],[c_15987,c_30])).

tff(c_16041,plain,(
    ! [A_989,B_990] : k4_xboole_0(k4_xboole_0(A_989,B_990),A_989) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14834,c_16018])).

tff(c_15502,plain,(
    ! [A_943,B_944,C_945] :
      ( r2_hidden('#skF_2'(A_943,B_944,C_945),A_943)
      | r2_hidden('#skF_3'(A_943,B_944,C_945),C_945)
      | k4_xboole_0(A_943,B_944) = C_945 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_19618,plain,(
    ! [A_1156,B_1157,B_1158,C_1159] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_1156,B_1157),B_1158,C_1159),A_1156)
      | r2_hidden('#skF_3'(k4_xboole_0(A_1156,B_1157),B_1158,C_1159),C_1159)
      | k4_xboole_0(k4_xboole_0(A_1156,B_1157),B_1158) = C_1159 ) ),
    inference(resolution,[status(thm)],[c_15502,c_12])).

tff(c_19651,plain,(
    ! [A_1156,B_1157,C_1159] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_1156,B_1157),A_1156,C_1159),C_1159)
      | k4_xboole_0(k4_xboole_0(A_1156,B_1157),A_1156) = C_1159 ) ),
    inference(resolution,[status(thm)],[c_19618,c_22])).

tff(c_19793,plain,(
    ! [A_1160,B_1161,C_1162] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_1160,B_1161),A_1160,C_1162),C_1162)
      | C_1162 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16041,c_19651])).

tff(c_19851,plain,(
    ! [A_883,C_1162] :
      ( r2_hidden('#skF_3'('#skF_9',A_883,C_1162),C_1162)
      | C_1162 = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14944,c_19793])).

tff(c_14926,plain,(
    ! [A_882] : k3_xboole_0(A_882,A_882) = A_882 ),
    inference(resolution,[status(thm)],[c_14922,c_34])).

tff(c_15746,plain,(
    ! [D_966,C_967,A_965,B_968,E_969] :
      ( r2_hidden('#skF_5'(A_965,D_966,C_967,B_968,E_969),k3_xboole_0(C_967,E_969))
      | ~ r2_hidden(A_965,k3_xboole_0(k2_zfmisc_1(B_968,C_967),k2_zfmisc_1(D_966,E_969))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_15764,plain,(
    ! [A_965,B_968,C_967] :
      ( r2_hidden('#skF_5'(A_965,B_968,C_967,B_968,C_967),k3_xboole_0(C_967,C_967))
      | ~ r2_hidden(A_965,k2_zfmisc_1(B_968,C_967)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14926,c_15746])).

tff(c_19348,plain,(
    ! [A_1147,B_1148,C_1149] :
      ( r2_hidden('#skF_5'(A_1147,B_1148,C_1149,B_1148,C_1149),C_1149)
      | ~ r2_hidden(A_1147,k2_zfmisc_1(B_1148,C_1149)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14926,c_15764])).

tff(c_14982,plain,(
    ! [A_889] : k4_xboole_0(A_889,A_889) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14834,c_14936])).

tff(c_14987,plain,(
    ! [D_11,A_889] :
      ( r2_hidden(D_11,A_889)
      | ~ r2_hidden(D_11,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14982,c_12])).

tff(c_19393,plain,(
    ! [A_1147,B_1148,A_889] :
      ( r2_hidden('#skF_5'(A_1147,B_1148,'#skF_9',B_1148,'#skF_9'),A_889)
      | ~ r2_hidden(A_1147,k2_zfmisc_1(B_1148,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_19348,c_14987])).

tff(c_15593,plain,(
    ! [E_956,B_955,C_954,A_952,D_953] :
      ( r2_hidden('#skF_4'(A_952,D_953,C_954,B_955,E_956),k3_xboole_0(B_955,D_953))
      | ~ r2_hidden(A_952,k3_xboole_0(k2_zfmisc_1(B_955,C_954),k2_zfmisc_1(D_953,E_956))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_15608,plain,(
    ! [A_952,B_955,C_954] :
      ( r2_hidden('#skF_4'(A_952,B_955,C_954,B_955,C_954),k3_xboole_0(B_955,B_955))
      | ~ r2_hidden(A_952,k2_zfmisc_1(B_955,C_954)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14926,c_15593])).

tff(c_15616,plain,(
    ! [A_952,B_955,C_954] :
      ( r2_hidden('#skF_4'(A_952,B_955,C_954,B_955,C_954),B_955)
      | ~ r2_hidden(A_952,k2_zfmisc_1(B_955,C_954)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14926,c_15608])).

tff(c_16937,plain,(
    ! [A_1061,B_1062,C_1063] :
      ( r2_hidden('#skF_4'(A_1061,B_1062,C_1063,B_1062,C_1063),B_1062)
      | ~ r2_hidden(A_1061,k2_zfmisc_1(B_1062,C_1063)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14926,c_15608])).

tff(c_14990,plain,(
    ! [D_11,A_889] :
      ( ~ r2_hidden(D_11,A_889)
      | ~ r2_hidden(D_11,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14982,c_10])).

tff(c_20478,plain,(
    ! [A_1185,B_1186,C_1187] :
      ( ~ r2_hidden('#skF_4'(A_1185,B_1186,C_1187,B_1186,C_1187),'#skF_9')
      | ~ r2_hidden(A_1185,k2_zfmisc_1(B_1186,C_1187)) ) ),
    inference(resolution,[status(thm)],[c_16937,c_14990])).

tff(c_20484,plain,(
    ! [A_1188,C_1189] : ~ r2_hidden(A_1188,k2_zfmisc_1('#skF_9',C_1189)) ),
    inference(resolution,[status(thm)],[c_15616,c_20478])).

tff(c_21087,plain,(
    ! [A_1198,B_1199] : ~ r2_hidden(A_1198,k2_zfmisc_1(B_1199,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_19393,c_20484])).

tff(c_21223,plain,(
    ! [B_1199] : k2_zfmisc_1(B_1199,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_19851,c_21087])).

tff(c_14831,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14839,plain,
    ( '#skF_6' = '#skF_9'
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14832,c_14832,c_14831])).

tff(c_14840,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_14839])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_6','#skF_7') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14854,plain,(
    k2_zfmisc_1('#skF_6','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14832,c_14840,c_14832,c_50])).

tff(c_21254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21223,c_14854])).

tff(c_21255,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_14839])).

tff(c_21269,plain,(
    k2_zfmisc_1('#skF_9','#skF_7') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14832,c_21255,c_14832,c_50])).

tff(c_27585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27554,c_21269])).

tff(c_27587,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_27588,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27587,c_36])).

tff(c_33427,plain,(
    ! [D_1900,A_1901,B_1902] :
      ( r2_hidden(D_1900,A_1901)
      | ~ r2_hidden(D_1900,k4_xboole_0(A_1901,B_1902)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34529,plain,(
    ! [A_2018,B_2019,B_2020] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_2018,B_2019),B_2020),A_2018)
      | r1_tarski(k4_xboole_0(A_2018,B_2019),B_2020) ) ),
    inference(resolution,[status(thm)],[c_6,c_33427])).

tff(c_34588,plain,(
    ! [A_2021,B_2022] : r1_tarski(k4_xboole_0(A_2021,B_2022),A_2021) ),
    inference(resolution,[status(thm)],[c_34529,c_4])).

tff(c_34617,plain,(
    ! [A_2023,B_2024] : k3_xboole_0(k4_xboole_0(A_2023,B_2024),A_2023) = k4_xboole_0(A_2023,B_2024) ),
    inference(resolution,[status(thm)],[c_34588,c_34])).

tff(c_34648,plain,(
    ! [A_2023,B_2024] : k5_xboole_0(k4_xboole_0(A_2023,B_2024),k4_xboole_0(A_2023,B_2024)) = k4_xboole_0(k4_xboole_0(A_2023,B_2024),A_2023) ),
    inference(superposition,[status(thm),theory(equality)],[c_34617,c_30])).

tff(c_34671,plain,(
    ! [A_2023,B_2024] : k4_xboole_0(k4_xboole_0(A_2023,B_2024),A_2023) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27588,c_34648])).

tff(c_33901,plain,(
    ! [A_1956,B_1957,C_1958] :
      ( r2_hidden('#skF_2'(A_1956,B_1957,C_1958),A_1956)
      | r2_hidden('#skF_3'(A_1956,B_1957,C_1958),C_1958)
      | k4_xboole_0(A_1956,B_1957) = C_1958 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38206,plain,(
    ! [A_2181,B_2182,B_2183,C_2184] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_2181,B_2182),B_2183,C_2184),A_2181)
      | r2_hidden('#skF_3'(k4_xboole_0(A_2181,B_2182),B_2183,C_2184),C_2184)
      | k4_xboole_0(k4_xboole_0(A_2181,B_2182),B_2183) = C_2184 ) ),
    inference(resolution,[status(thm)],[c_33901,c_12])).

tff(c_38242,plain,(
    ! [A_2181,B_2182,C_2184] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_2181,B_2182),A_2181,C_2184),C_2184)
      | k4_xboole_0(k4_xboole_0(A_2181,B_2182),A_2181) = C_2184 ) ),
    inference(resolution,[status(thm)],[c_38206,c_22])).

tff(c_38354,plain,(
    ! [A_2181,B_2182,C_2184] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_2181,B_2182),A_2181,C_2184),C_2184)
      | C_2184 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34671,c_38242])).

tff(c_33416,plain,(
    ! [A_1898,B_1899] :
      ( r2_hidden('#skF_1'(A_1898,B_1899),A_1898)
      | r1_tarski(A_1898,B_1899) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33433,plain,(
    ! [A_1903] : r1_tarski(A_1903,A_1903) ),
    inference(resolution,[status(thm)],[c_33416,c_4])).

tff(c_33437,plain,(
    ! [A_1903] : k3_xboole_0(A_1903,A_1903) = A_1903 ),
    inference(resolution,[status(thm)],[c_33433,c_34])).

tff(c_34138,plain,(
    ! [A_1974,B_1977,C_1976,E_1978,D_1975] :
      ( r2_hidden('#skF_5'(A_1974,D_1975,C_1976,B_1977,E_1978),k3_xboole_0(C_1976,E_1978))
      | ~ r2_hidden(A_1974,k3_xboole_0(k2_zfmisc_1(B_1977,C_1976),k2_zfmisc_1(D_1975,E_1978))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34153,plain,(
    ! [A_1974,B_1977,C_1976] :
      ( r2_hidden('#skF_5'(A_1974,B_1977,C_1976,B_1977,C_1976),k3_xboole_0(C_1976,C_1976))
      | ~ r2_hidden(A_1974,k2_zfmisc_1(B_1977,C_1976)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33437,c_34138])).

tff(c_37572,plain,(
    ! [A_2150,B_2151,C_2152] :
      ( r2_hidden('#skF_5'(A_2150,B_2151,C_2152,B_2151,C_2152),C_2152)
      | ~ r2_hidden(A_2150,k2_zfmisc_1(B_2151,C_2152)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33437,c_34153])).

tff(c_33441,plain,(
    ! [A_1904] : k3_xboole_0(A_1904,A_1904) = A_1904 ),
    inference(resolution,[status(thm)],[c_33433,c_34])).

tff(c_33447,plain,(
    ! [A_1904] : k5_xboole_0(A_1904,A_1904) = k4_xboole_0(A_1904,A_1904) ),
    inference(superposition,[status(thm),theory(equality)],[c_33441,c_30])).

tff(c_33492,plain,(
    ! [A_1910] : k4_xboole_0(A_1910,A_1910) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27588,c_33447])).

tff(c_33497,plain,(
    ! [D_11,A_1910] :
      ( r2_hidden(D_11,A_1910)
      | ~ r2_hidden(D_11,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33492,c_12])).

tff(c_37617,plain,(
    ! [A_2150,B_2151,A_1910] :
      ( r2_hidden('#skF_5'(A_2150,B_2151,'#skF_8',B_2151,'#skF_8'),A_1910)
      | ~ r2_hidden(A_2150,k2_zfmisc_1(B_2151,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_37572,c_33497])).

tff(c_38003,plain,(
    ! [A_2169,B_2170,A_2171] :
      ( r2_hidden('#skF_5'(A_2169,B_2170,'#skF_8',B_2170,'#skF_8'),A_2171)
      | ~ r2_hidden(A_2169,k2_zfmisc_1(B_2170,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_37572,c_33497])).

tff(c_39610,plain,(
    ! [A_2232,B_2233,B_2234] :
      ( ~ r2_hidden('#skF_5'(A_2232,B_2233,'#skF_8',B_2233,'#skF_8'),B_2234)
      | ~ r2_hidden(A_2232,k2_zfmisc_1(B_2233,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_38003,c_10])).

tff(c_39630,plain,(
    ! [A_2235,B_2236] : ~ r2_hidden(A_2235,k2_zfmisc_1(B_2236,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_37617,c_39610])).

tff(c_39786,plain,(
    ! [B_2236] : k2_zfmisc_1(B_2236,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38354,c_39630])).

tff(c_27666,plain,(
    ! [A_1569,B_1570] :
      ( ~ r2_hidden('#skF_1'(A_1569,B_1570),B_1570)
      | r1_tarski(A_1569,B_1570) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27672,plain,(
    ! [A_1571] : r1_tarski(A_1571,A_1571) ),
    inference(resolution,[status(thm)],[c_6,c_27666])).

tff(c_27680,plain,(
    ! [A_1572] : k3_xboole_0(A_1572,A_1572) = A_1572 ),
    inference(resolution,[status(thm)],[c_27672,c_34])).

tff(c_27686,plain,(
    ! [A_1572] : k5_xboole_0(A_1572,A_1572) = k4_xboole_0(A_1572,A_1572) ),
    inference(superposition,[status(thm),theory(equality)],[c_27680,c_30])).

tff(c_27694,plain,(
    ! [A_1572] : k4_xboole_0(A_1572,A_1572) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27588,c_27686])).

tff(c_28251,plain,(
    ! [A_1633,B_1634,C_1635] :
      ( r2_hidden('#skF_2'(A_1633,B_1634,C_1635),A_1633)
      | r2_hidden('#skF_3'(A_1633,B_1634,C_1635),C_1635)
      | k4_xboole_0(A_1633,B_1634) = C_1635 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28258,plain,(
    ! [A_1633,C_1635] :
      ( r2_hidden('#skF_3'(A_1633,A_1633,C_1635),C_1635)
      | k4_xboole_0(A_1633,A_1633) = C_1635 ) ),
    inference(resolution,[status(thm)],[c_28251,c_22])).

tff(c_28289,plain,(
    ! [A_1633,C_1635] :
      ( r2_hidden('#skF_3'(A_1633,A_1633,C_1635),C_1635)
      | C_1635 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27694,c_28258])).

tff(c_27676,plain,(
    ! [A_1571] : k3_xboole_0(A_1571,A_1571) = A_1571 ),
    inference(resolution,[status(thm)],[c_27672,c_34])).

tff(c_28487,plain,(
    ! [E_1660,B_1659,C_1658,A_1656,D_1657] :
      ( r2_hidden('#skF_4'(A_1656,D_1657,C_1658,B_1659,E_1660),k3_xboole_0(B_1659,D_1657))
      | ~ r2_hidden(A_1656,k3_xboole_0(k2_zfmisc_1(B_1659,C_1658),k2_zfmisc_1(D_1657,E_1660))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28505,plain,(
    ! [A_1656,B_1659,C_1658] :
      ( r2_hidden('#skF_4'(A_1656,B_1659,C_1658,B_1659,C_1658),k3_xboole_0(B_1659,B_1659))
      | ~ r2_hidden(A_1656,k2_zfmisc_1(B_1659,C_1658)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27676,c_28487])).

tff(c_29751,plain,(
    ! [A_1752,B_1753,C_1754] :
      ( r2_hidden('#skF_4'(A_1752,B_1753,C_1754,B_1753,C_1754),B_1753)
      | ~ r2_hidden(A_1752,k2_zfmisc_1(B_1753,C_1754)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27676,c_28505])).

tff(c_27739,plain,(
    ! [A_1581] : k4_xboole_0(A_1581,A_1581) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27588,c_27686])).

tff(c_27747,plain,(
    ! [D_11,A_1581] :
      ( r2_hidden(D_11,A_1581)
      | ~ r2_hidden(D_11,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27739,c_12])).

tff(c_29785,plain,(
    ! [A_1752,C_1754,A_1581] :
      ( r2_hidden('#skF_4'(A_1752,'#skF_8',C_1754,'#skF_8',C_1754),A_1581)
      | ~ r2_hidden(A_1752,k2_zfmisc_1('#skF_8',C_1754)) ) ),
    inference(resolution,[status(thm)],[c_29751,c_27747])).

tff(c_28377,plain,(
    ! [C_1646,E_1648,B_1647,D_1645,A_1644] :
      ( r2_hidden('#skF_5'(A_1644,D_1645,C_1646,B_1647,E_1648),k3_xboole_0(C_1646,E_1648))
      | ~ r2_hidden(A_1644,k3_xboole_0(k2_zfmisc_1(B_1647,C_1646),k2_zfmisc_1(D_1645,E_1648))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28392,plain,(
    ! [A_1644,B_1647,C_1646] :
      ( r2_hidden('#skF_5'(A_1644,B_1647,C_1646,B_1647,C_1646),k3_xboole_0(C_1646,C_1646))
      | ~ r2_hidden(A_1644,k2_zfmisc_1(B_1647,C_1646)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27676,c_28377])).

tff(c_28400,plain,(
    ! [A_1644,B_1647,C_1646] :
      ( r2_hidden('#skF_5'(A_1644,B_1647,C_1646,B_1647,C_1646),C_1646)
      | ~ r2_hidden(A_1644,k2_zfmisc_1(B_1647,C_1646)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27676,c_28392])).

tff(c_29713,plain,(
    ! [A_1749,B_1750,C_1751] :
      ( r2_hidden('#skF_5'(A_1749,B_1750,C_1751,B_1750,C_1751),C_1751)
      | ~ r2_hidden(A_1749,k2_zfmisc_1(B_1750,C_1751)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27676,c_28392])).

tff(c_27744,plain,(
    ! [D_11,A_1581] :
      ( ~ r2_hidden(D_11,A_1581)
      | ~ r2_hidden(D_11,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27739,c_10])).

tff(c_32874,plain,(
    ! [A_1867,B_1868,C_1869] :
      ( ~ r2_hidden('#skF_5'(A_1867,B_1868,C_1869,B_1868,C_1869),'#skF_8')
      | ~ r2_hidden(A_1867,k2_zfmisc_1(B_1868,C_1869)) ) ),
    inference(resolution,[status(thm)],[c_29713,c_27744])).

tff(c_32880,plain,(
    ! [A_1870,B_1871] : ~ r2_hidden(A_1870,k2_zfmisc_1(B_1871,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_28400,c_32874])).

tff(c_33179,plain,(
    ! [A_1874,C_1875] : ~ r2_hidden(A_1874,k2_zfmisc_1('#skF_8',C_1875)) ),
    inference(resolution,[status(thm)],[c_29785,c_32880])).

tff(c_33306,plain,(
    ! [C_1875] : k2_zfmisc_1('#skF_8',C_1875) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_28289,c_33179])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_27602,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27587,c_27587,c_27587,c_56])).

tff(c_27603,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_27602])).

tff(c_27586,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_27593,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27587,c_27586])).

tff(c_27604,plain,(
    k2_zfmisc_1('#skF_8','#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27603,c_27593])).

tff(c_33348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33306,c_27604])).

tff(c_33349,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_27602])).

tff(c_33351,plain,(
    k2_zfmisc_1('#skF_6','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33349,c_27593])).

tff(c_39817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39786,c_33351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:09:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.77/4.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/4.87  
% 10.94/4.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/4.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 10.94/4.87  
% 10.94/4.87  %Foreground sorts:
% 10.94/4.87  
% 10.94/4.87  
% 10.94/4.87  %Background operators:
% 10.94/4.87  
% 10.94/4.87  
% 10.94/4.87  %Foreground operators:
% 10.94/4.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.94/4.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.94/4.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.94/4.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.94/4.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.94/4.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 10.94/4.87  tff('#skF_7', type, '#skF_7': $i).
% 10.94/4.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.94/4.87  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 10.94/4.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.94/4.87  tff('#skF_6', type, '#skF_6': $i).
% 10.94/4.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.94/4.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.94/4.87  tff('#skF_9', type, '#skF_9': $i).
% 10.94/4.87  tff('#skF_8', type, '#skF_8': $i).
% 10.94/4.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.94/4.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.94/4.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.94/4.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.94/4.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.94/4.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.94/4.87  
% 10.94/4.90  tff(f_80, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.94/4.90  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.94/4.90  tff(f_73, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 10.94/4.90  tff(f_56, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.94/4.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.94/4.90  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.94/4.90  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.94/4.90  tff(f_67, axiom, (![A, B, C, D, E]: ~(r2_hidden(A, k3_xboole_0(k2_zfmisc_1(B, C), k2_zfmisc_1(D, E))) & (![F, G]: ~(((A = k4_tarski(F, G)) & r2_hidden(F, k3_xboole_0(B, D))) & r2_hidden(G, k3_xboole_0(C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_zfmisc_1)).
% 10.94/4.90  tff(c_52, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.94/4.90  tff(c_69, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_52])).
% 10.94/4.90  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_728, plain, (![A_115, B_116, C_117]: (~r2_hidden('#skF_2'(A_115, B_116, C_117), C_117) | r2_hidden('#skF_3'(A_115, B_116, C_117), C_117) | k4_xboole_0(A_115, B_116)=C_117)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_737, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k4_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_728])).
% 10.94/4.90  tff(c_54, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.94/4.90  tff(c_68, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_54])).
% 10.94/4.90  tff(c_60, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.94/4.90  tff(c_75, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 10.94/4.90  tff(c_416, plain, (![A_92, B_93, C_94, D_95]: (r2_hidden(k4_tarski(A_92, B_93), k2_zfmisc_1(C_94, D_95)) | ~r2_hidden(B_93, D_95) | ~r2_hidden(A_92, C_94))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.94/4.90  tff(c_429, plain, (![A_92, B_93]: (r2_hidden(k4_tarski(A_92, B_93), k1_xboole_0) | ~r2_hidden(B_93, '#skF_9') | ~r2_hidden(A_92, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_416])).
% 10.94/4.90  tff(c_606, plain, (![A_107, B_108]: (r2_hidden(k4_tarski(A_107, B_108), k1_xboole_0) | ~r2_hidden(B_108, '#skF_9') | ~r2_hidden(A_107, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_416])).
% 10.94/4.90  tff(c_36, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.94/4.90  tff(c_129, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.90  tff(c_145, plain, (![A_56]: (r1_tarski(A_56, A_56))), inference(resolution, [status(thm)], [c_129, c_4])).
% 10.94/4.90  tff(c_34, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.94/4.90  tff(c_153, plain, (![A_57]: (k3_xboole_0(A_57, A_57)=A_57)), inference(resolution, [status(thm)], [c_145, c_34])).
% 10.94/4.90  tff(c_30, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.94/4.90  tff(c_159, plain, (![A_57]: (k5_xboole_0(A_57, A_57)=k4_xboole_0(A_57, A_57))), inference(superposition, [status(thm), theory('equality')], [c_153, c_30])).
% 10.94/4.90  tff(c_208, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_159])).
% 10.94/4.90  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_213, plain, (![D_11, A_67]: (~r2_hidden(D_11, A_67) | ~r2_hidden(D_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_10])).
% 10.94/4.90  tff(c_829, plain, (![A_122, B_123]: (~r2_hidden(k4_tarski(A_122, B_123), k1_xboole_0) | ~r2_hidden(B_123, '#skF_9') | ~r2_hidden(A_122, '#skF_8'))), inference(resolution, [status(thm)], [c_606, c_213])).
% 10.94/4.90  tff(c_833, plain, (![B_93, A_92]: (~r2_hidden(B_93, '#skF_9') | ~r2_hidden(A_92, '#skF_8'))), inference(resolution, [status(thm)], [c_429, c_829])).
% 10.94/4.90  tff(c_836, plain, (![A_124]: (~r2_hidden(A_124, '#skF_8'))), inference(splitLeft, [status(thm)], [c_833])).
% 10.94/4.90  tff(c_859, plain, (![B_126]: (k4_xboole_0('#skF_8', B_126)='#skF_8')), inference(resolution, [status(thm)], [c_737, c_836])).
% 10.94/4.90  tff(c_167, plain, (![A_57]: (k4_xboole_0(A_57, A_57)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_159])).
% 10.94/4.90  tff(c_876, plain, (k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_859, c_167])).
% 10.94/4.90  tff(c_891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_876])).
% 10.94/4.90  tff(c_894, plain, (![B_127]: (~r2_hidden(B_127, '#skF_9'))), inference(splitRight, [status(thm)], [c_833])).
% 10.94/4.90  tff(c_927, plain, (![B_132]: (k4_xboole_0('#skF_9', B_132)='#skF_9')), inference(resolution, [status(thm)], [c_737, c_894])).
% 10.94/4.90  tff(c_944, plain, (k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_927, c_167])).
% 10.94/4.90  tff(c_959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_944])).
% 10.94/4.90  tff(c_960, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_60])).
% 10.94/4.90  tff(c_962, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_960])).
% 10.94/4.90  tff(c_966, plain, (![A_20]: (k5_xboole_0(A_20, A_20)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_962, c_36])).
% 10.94/4.90  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.90  tff(c_1033, plain, (![A_145, B_146]: (~r2_hidden('#skF_1'(A_145, B_146), B_146) | r1_tarski(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.90  tff(c_1045, plain, (![A_150]: (r1_tarski(A_150, A_150))), inference(resolution, [status(thm)], [c_6, c_1033])).
% 10.94/4.90  tff(c_1053, plain, (![A_151]: (k3_xboole_0(A_151, A_151)=A_151)), inference(resolution, [status(thm)], [c_1045, c_34])).
% 10.94/4.90  tff(c_1059, plain, (![A_151]: (k5_xboole_0(A_151, A_151)=k4_xboole_0(A_151, A_151))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_30])).
% 10.94/4.90  tff(c_1067, plain, (![A_151]: (k4_xboole_0(A_151, A_151)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_966, c_1059])).
% 10.94/4.90  tff(c_1075, plain, (![D_153, A_154, B_155]: (r2_hidden(D_153, A_154) | ~r2_hidden(D_153, k4_xboole_0(A_154, B_155)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_2102, plain, (![A_262, B_263, B_264]: (r2_hidden('#skF_1'(k4_xboole_0(A_262, B_263), B_264), A_262) | r1_tarski(k4_xboole_0(A_262, B_263), B_264))), inference(resolution, [status(thm)], [c_6, c_1075])).
% 10.94/4.90  tff(c_2157, plain, (![A_265, B_266]: (r1_tarski(k4_xboole_0(A_265, B_266), A_265))), inference(resolution, [status(thm)], [c_2102, c_4])).
% 10.94/4.90  tff(c_2230, plain, (![A_272, B_273]: (k3_xboole_0(k4_xboole_0(A_272, B_273), A_272)=k4_xboole_0(A_272, B_273))), inference(resolution, [status(thm)], [c_2157, c_34])).
% 10.94/4.90  tff(c_2261, plain, (![A_272, B_273]: (k5_xboole_0(k4_xboole_0(A_272, B_273), k4_xboole_0(A_272, B_273))=k4_xboole_0(k4_xboole_0(A_272, B_273), A_272))), inference(superposition, [status(thm), theory('equality')], [c_2230, c_30])).
% 10.94/4.90  tff(c_2284, plain, (![A_272, B_273]: (k4_xboole_0(k4_xboole_0(A_272, B_273), A_272)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_966, c_2261])).
% 10.94/4.90  tff(c_1432, plain, (![A_195, B_196, C_197]: (r2_hidden('#skF_2'(A_195, B_196, C_197), A_195) | r2_hidden('#skF_3'(A_195, B_196, C_197), C_197) | k4_xboole_0(A_195, B_196)=C_197)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_5314, plain, (![A_405, B_406, B_407, C_408]: (r2_hidden('#skF_2'(k4_xboole_0(A_405, B_406), B_407, C_408), A_405) | r2_hidden('#skF_3'(k4_xboole_0(A_405, B_406), B_407, C_408), C_408) | k4_xboole_0(k4_xboole_0(A_405, B_406), B_407)=C_408)), inference(resolution, [status(thm)], [c_1432, c_12])).
% 10.94/4.90  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_5347, plain, (![A_405, B_406, C_408]: (r2_hidden('#skF_3'(k4_xboole_0(A_405, B_406), A_405, C_408), C_408) | k4_xboole_0(k4_xboole_0(A_405, B_406), A_405)=C_408)), inference(resolution, [status(thm)], [c_5314, c_22])).
% 10.94/4.90  tff(c_5484, plain, (![A_409, B_410, C_411]: (r2_hidden('#skF_3'(k4_xboole_0(A_409, B_410), A_409, C_411), C_411) | C_411='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2284, c_5347])).
% 10.94/4.90  tff(c_5542, plain, (![A_151, C_411]: (r2_hidden('#skF_3'('#skF_7', A_151, C_411), C_411) | C_411='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1067, c_5484])).
% 10.94/4.90  tff(c_1049, plain, (![A_150]: (k3_xboole_0(A_150, A_150)=A_150)), inference(resolution, [status(thm)], [c_1045, c_34])).
% 10.94/4.90  tff(c_1725, plain, (![A_218, B_221, E_222, D_219, C_220]: (r2_hidden('#skF_5'(A_218, D_219, C_220, B_221, E_222), k3_xboole_0(C_220, E_222)) | ~r2_hidden(A_218, k3_xboole_0(k2_zfmisc_1(B_221, C_220), k2_zfmisc_1(D_219, E_222))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.90  tff(c_1740, plain, (![A_218, B_221, C_220]: (r2_hidden('#skF_5'(A_218, B_221, C_220, B_221, C_220), k3_xboole_0(C_220, C_220)) | ~r2_hidden(A_218, k2_zfmisc_1(B_221, C_220)))), inference(superposition, [status(thm), theory('equality')], [c_1049, c_1725])).
% 10.94/4.90  tff(c_4443, plain, (![A_379, B_380, C_381]: (r2_hidden('#skF_5'(A_379, B_380, C_381, B_380, C_381), C_381) | ~r2_hidden(A_379, k2_zfmisc_1(B_380, C_381)))), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1740])).
% 10.94/4.90  tff(c_1106, plain, (![A_157]: (k4_xboole_0(A_157, A_157)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_966, c_1059])).
% 10.94/4.90  tff(c_1111, plain, (![D_11, A_157]: (r2_hidden(D_11, A_157) | ~r2_hidden(D_11, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_12])).
% 10.94/4.90  tff(c_4488, plain, (![A_379, B_380, A_157]: (r2_hidden('#skF_5'(A_379, B_380, '#skF_7', B_380, '#skF_7'), A_157) | ~r2_hidden(A_379, k2_zfmisc_1(B_380, '#skF_7')))), inference(resolution, [status(thm)], [c_4443, c_1111])).
% 10.94/4.90  tff(c_6186, plain, (![A_438, B_439, A_440]: (r2_hidden('#skF_5'(A_438, B_439, '#skF_7', B_439, '#skF_7'), A_440) | ~r2_hidden(A_438, k2_zfmisc_1(B_439, '#skF_7')))), inference(resolution, [status(thm)], [c_4443, c_1111])).
% 10.94/4.90  tff(c_7477, plain, (![A_490, B_491, B_492]: (~r2_hidden('#skF_5'(A_490, B_491, '#skF_7', B_491, '#skF_7'), B_492) | ~r2_hidden(A_490, k2_zfmisc_1(B_491, '#skF_7')))), inference(resolution, [status(thm)], [c_6186, c_10])).
% 10.94/4.90  tff(c_7497, plain, (![A_493, B_494]: (~r2_hidden(A_493, k2_zfmisc_1(B_494, '#skF_7')))), inference(resolution, [status(thm)], [c_4488, c_7477])).
% 10.94/4.90  tff(c_7663, plain, (![B_494]: (k2_zfmisc_1(B_494, '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_5542, c_7497])).
% 10.94/4.90  tff(c_58, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!=k1_xboole_0 | k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.94/4.90  tff(c_963, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 10.94/4.90  tff(c_971, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_962, c_963])).
% 10.94/4.90  tff(c_7694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7663, c_971])).
% 10.94/4.90  tff(c_7695, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 10.94/4.90  tff(c_7704, plain, (k2_zfmisc_1('#skF_8', '#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_962, c_7695])).
% 10.94/4.90  tff(c_961, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 10.94/4.90  tff(c_7725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7704, c_962, c_961])).
% 10.94/4.90  tff(c_7726, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_960])).
% 10.94/4.90  tff(c_7731, plain, (![A_20]: (k5_xboole_0(A_20, A_20)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7726, c_36])).
% 10.94/4.90  tff(c_7800, plain, (![A_511, B_512]: (r2_hidden('#skF_1'(A_511, B_512), A_511) | r1_tarski(A_511, B_512))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.90  tff(c_7811, plain, (![A_513]: (r1_tarski(A_513, A_513))), inference(resolution, [status(thm)], [c_7800, c_4])).
% 10.94/4.90  tff(c_7819, plain, (![A_514]: (k3_xboole_0(A_514, A_514)=A_514)), inference(resolution, [status(thm)], [c_7811, c_34])).
% 10.94/4.90  tff(c_7825, plain, (![A_514]: (k5_xboole_0(A_514, A_514)=k4_xboole_0(A_514, A_514))), inference(superposition, [status(thm), theory('equality')], [c_7819, c_30])).
% 10.94/4.90  tff(c_7833, plain, (![A_514]: (k4_xboole_0(A_514, A_514)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7731, c_7825])).
% 10.94/4.90  tff(c_7836, plain, (![D_515, A_516, B_517]: (r2_hidden(D_515, A_516) | ~r2_hidden(D_515, k4_xboole_0(A_516, B_517)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_8874, plain, (![A_626, B_627, B_628]: (r2_hidden('#skF_1'(k4_xboole_0(A_626, B_627), B_628), A_626) | r1_tarski(k4_xboole_0(A_626, B_627), B_628))), inference(resolution, [status(thm)], [c_6, c_7836])).
% 10.94/4.90  tff(c_8929, plain, (![A_629, B_630]: (r1_tarski(k4_xboole_0(A_629, B_630), A_629))), inference(resolution, [status(thm)], [c_8874, c_4])).
% 10.94/4.90  tff(c_9002, plain, (![A_636, B_637]: (k3_xboole_0(k4_xboole_0(A_636, B_637), A_636)=k4_xboole_0(A_636, B_637))), inference(resolution, [status(thm)], [c_8929, c_34])).
% 10.94/4.90  tff(c_9033, plain, (![A_636, B_637]: (k5_xboole_0(k4_xboole_0(A_636, B_637), k4_xboole_0(A_636, B_637))=k4_xboole_0(k4_xboole_0(A_636, B_637), A_636))), inference(superposition, [status(thm), theory('equality')], [c_9002, c_30])).
% 10.94/4.90  tff(c_9056, plain, (![A_636, B_637]: (k4_xboole_0(k4_xboole_0(A_636, B_637), A_636)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7731, c_9033])).
% 10.94/4.90  tff(c_8198, plain, (![A_557, B_558, C_559]: (r2_hidden('#skF_2'(A_557, B_558, C_559), A_557) | r2_hidden('#skF_3'(A_557, B_558, C_559), C_559) | k4_xboole_0(A_557, B_558)=C_559)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_13040, plain, (![A_811, B_812, B_813, C_814]: (r2_hidden('#skF_2'(k4_xboole_0(A_811, B_812), B_813, C_814), A_811) | r2_hidden('#skF_3'(k4_xboole_0(A_811, B_812), B_813, C_814), C_814) | k4_xboole_0(k4_xboole_0(A_811, B_812), B_813)=C_814)), inference(resolution, [status(thm)], [c_8198, c_12])).
% 10.94/4.90  tff(c_13073, plain, (![A_811, B_812, C_814]: (r2_hidden('#skF_3'(k4_xboole_0(A_811, B_812), A_811, C_814), C_814) | k4_xboole_0(k4_xboole_0(A_811, B_812), A_811)=C_814)), inference(resolution, [status(thm)], [c_13040, c_22])).
% 10.94/4.90  tff(c_13215, plain, (![A_815, B_816, C_817]: (r2_hidden('#skF_3'(k4_xboole_0(A_815, B_816), A_815, C_817), C_817) | C_817='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9056, c_13073])).
% 10.94/4.90  tff(c_13273, plain, (![A_514, C_817]: (r2_hidden('#skF_3'('#skF_6', A_514, C_817), C_817) | C_817='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7833, c_13215])).
% 10.94/4.90  tff(c_7815, plain, (![A_513]: (k3_xboole_0(A_513, A_513)=A_513)), inference(resolution, [status(thm)], [c_7811, c_34])).
% 10.94/4.90  tff(c_8497, plain, (![C_584, B_585, E_586, D_583, A_582]: (r2_hidden('#skF_4'(A_582, D_583, C_584, B_585, E_586), k3_xboole_0(B_585, D_583)) | ~r2_hidden(A_582, k3_xboole_0(k2_zfmisc_1(B_585, C_584), k2_zfmisc_1(D_583, E_586))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.90  tff(c_8512, plain, (![A_582, B_585, C_584]: (r2_hidden('#skF_4'(A_582, B_585, C_584, B_585, C_584), k3_xboole_0(B_585, B_585)) | ~r2_hidden(A_582, k2_zfmisc_1(B_585, C_584)))), inference(superposition, [status(thm), theory('equality')], [c_7815, c_8497])).
% 10.94/4.90  tff(c_11923, plain, (![A_762, B_763, C_764]: (r2_hidden('#skF_4'(A_762, B_763, C_764, B_763, C_764), B_763) | ~r2_hidden(A_762, k2_zfmisc_1(B_763, C_764)))), inference(demodulation, [status(thm), theory('equality')], [c_7815, c_8512])).
% 10.94/4.90  tff(c_7871, plain, (![A_520]: (k4_xboole_0(A_520, A_520)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7731, c_7825])).
% 10.94/4.90  tff(c_7876, plain, (![D_11, A_520]: (r2_hidden(D_11, A_520) | ~r2_hidden(D_11, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7871, c_12])).
% 10.94/4.90  tff(c_11968, plain, (![A_762, C_764, A_520]: (r2_hidden('#skF_4'(A_762, '#skF_6', C_764, '#skF_6', C_764), A_520) | ~r2_hidden(A_762, k2_zfmisc_1('#skF_6', C_764)))), inference(resolution, [status(thm)], [c_11923, c_7876])).
% 10.94/4.90  tff(c_8540, plain, (![D_590, A_589, E_593, C_591, B_592]: (r2_hidden('#skF_5'(A_589, D_590, C_591, B_592, E_593), k3_xboole_0(C_591, E_593)) | ~r2_hidden(A_589, k3_xboole_0(k2_zfmisc_1(B_592, C_591), k2_zfmisc_1(D_590, E_593))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.90  tff(c_8555, plain, (![A_589, B_592, C_591]: (r2_hidden('#skF_5'(A_589, B_592, C_591, B_592, C_591), k3_xboole_0(C_591, C_591)) | ~r2_hidden(A_589, k2_zfmisc_1(B_592, C_591)))), inference(superposition, [status(thm), theory('equality')], [c_7815, c_8540])).
% 10.94/4.90  tff(c_11874, plain, (![A_759, B_760, C_761]: (r2_hidden('#skF_5'(A_759, B_760, C_761, B_760, C_761), C_761) | ~r2_hidden(A_759, k2_zfmisc_1(B_760, C_761)))), inference(demodulation, [status(thm), theory('equality')], [c_7815, c_8555])).
% 10.94/4.90  tff(c_11919, plain, (![A_759, B_760, A_520]: (r2_hidden('#skF_5'(A_759, B_760, '#skF_6', B_760, '#skF_6'), A_520) | ~r2_hidden(A_759, k2_zfmisc_1(B_760, '#skF_6')))), inference(resolution, [status(thm)], [c_11874, c_7876])).
% 10.94/4.90  tff(c_12460, plain, (![A_782, B_783, A_784]: (r2_hidden('#skF_5'(A_782, B_783, '#skF_6', B_783, '#skF_6'), A_784) | ~r2_hidden(A_782, k2_zfmisc_1(B_783, '#skF_6')))), inference(resolution, [status(thm)], [c_11874, c_7876])).
% 10.94/4.90  tff(c_14011, plain, (![A_848, B_849, B_850]: (~r2_hidden('#skF_5'(A_848, B_849, '#skF_6', B_849, '#skF_6'), B_850) | ~r2_hidden(A_848, k2_zfmisc_1(B_849, '#skF_6')))), inference(resolution, [status(thm)], [c_12460, c_10])).
% 10.94/4.90  tff(c_14031, plain, (![A_851, B_852]: (~r2_hidden(A_851, k2_zfmisc_1(B_852, '#skF_6')))), inference(resolution, [status(thm)], [c_11919, c_14011])).
% 10.94/4.90  tff(c_14609, plain, (![A_859, C_860]: (~r2_hidden(A_859, k2_zfmisc_1('#skF_6', C_860)))), inference(resolution, [status(thm)], [c_11968, c_14031])).
% 10.94/4.90  tff(c_14777, plain, (![C_860]: (k2_zfmisc_1('#skF_6', C_860)='#skF_6')), inference(resolution, [status(thm)], [c_13273, c_14609])).
% 10.94/4.90  tff(c_7728, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 10.94/4.90  tff(c_7737, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7726, c_7728])).
% 10.94/4.90  tff(c_14813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14777, c_7737])).
% 10.94/4.90  tff(c_14814, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 10.94/4.90  tff(c_14824, plain, (k2_zfmisc_1('#skF_8', '#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7726, c_14814])).
% 10.94/4.90  tff(c_14830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14824, c_7726, c_961])).
% 10.94/4.90  tff(c_14832, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 10.94/4.90  tff(c_14834, plain, (![A_20]: (k5_xboole_0(A_20, A_20)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14832, c_36])).
% 10.94/4.90  tff(c_21340, plain, (![A_1222, B_1223]: (~r2_hidden('#skF_1'(A_1222, B_1223), B_1223) | r1_tarski(A_1222, B_1223))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.90  tff(c_21346, plain, (![A_1224]: (r1_tarski(A_1224, A_1224))), inference(resolution, [status(thm)], [c_6, c_21340])).
% 10.94/4.90  tff(c_21354, plain, (![A_1225]: (k3_xboole_0(A_1225, A_1225)=A_1225)), inference(resolution, [status(thm)], [c_21346, c_34])).
% 10.94/4.90  tff(c_21360, plain, (![A_1225]: (k5_xboole_0(A_1225, A_1225)=k4_xboole_0(A_1225, A_1225))), inference(superposition, [status(thm), theory('equality')], [c_21354, c_30])).
% 10.94/4.90  tff(c_21368, plain, (![A_1225]: (k4_xboole_0(A_1225, A_1225)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14834, c_21360])).
% 10.94/4.90  tff(c_21313, plain, (![A_1215, B_1216]: (r2_hidden('#skF_1'(A_1215, B_1216), A_1215) | r1_tarski(A_1215, B_1216))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.90  tff(c_22345, plain, (![A_1326, B_1327, B_1328]: (r2_hidden('#skF_1'(k4_xboole_0(A_1326, B_1327), B_1328), A_1326) | r1_tarski(k4_xboole_0(A_1326, B_1327), B_1328))), inference(resolution, [status(thm)], [c_21313, c_12])).
% 10.94/4.90  tff(c_22394, plain, (![A_1329, B_1330]: (r1_tarski(k4_xboole_0(A_1329, B_1330), A_1329))), inference(resolution, [status(thm)], [c_22345, c_4])).
% 10.94/4.90  tff(c_22462, plain, (![A_1336, B_1337]: (k3_xboole_0(k4_xboole_0(A_1336, B_1337), A_1336)=k4_xboole_0(A_1336, B_1337))), inference(resolution, [status(thm)], [c_22394, c_34])).
% 10.94/4.90  tff(c_22493, plain, (![A_1336, B_1337]: (k5_xboole_0(k4_xboole_0(A_1336, B_1337), k4_xboole_0(A_1336, B_1337))=k4_xboole_0(k4_xboole_0(A_1336, B_1337), A_1336))), inference(superposition, [status(thm), theory('equality')], [c_22462, c_30])).
% 10.94/4.90  tff(c_22516, plain, (![A_1336, B_1337]: (k4_xboole_0(k4_xboole_0(A_1336, B_1337), A_1336)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14834, c_22493])).
% 10.94/4.90  tff(c_21818, plain, (![A_1277, B_1278, C_1279]: (r2_hidden('#skF_2'(A_1277, B_1278, C_1279), A_1277) | r2_hidden('#skF_3'(A_1277, B_1278, C_1279), C_1279) | k4_xboole_0(A_1277, B_1278)=C_1279)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_25934, plain, (![A_1492, B_1493, B_1494, C_1495]: (r2_hidden('#skF_2'(k4_xboole_0(A_1492, B_1493), B_1494, C_1495), A_1492) | r2_hidden('#skF_3'(k4_xboole_0(A_1492, B_1493), B_1494, C_1495), C_1495) | k4_xboole_0(k4_xboole_0(A_1492, B_1493), B_1494)=C_1495)), inference(resolution, [status(thm)], [c_21818, c_12])).
% 10.94/4.90  tff(c_25967, plain, (![A_1492, B_1493, C_1495]: (r2_hidden('#skF_3'(k4_xboole_0(A_1492, B_1493), A_1492, C_1495), C_1495) | k4_xboole_0(k4_xboole_0(A_1492, B_1493), A_1492)=C_1495)), inference(resolution, [status(thm)], [c_25934, c_22])).
% 10.94/4.90  tff(c_26109, plain, (![A_1496, B_1497, C_1498]: (r2_hidden('#skF_3'(k4_xboole_0(A_1496, B_1497), A_1496, C_1498), C_1498) | C_1498='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_22516, c_25967])).
% 10.94/4.90  tff(c_26167, plain, (![A_1225, C_1498]: (r2_hidden('#skF_3'('#skF_9', A_1225, C_1498), C_1498) | C_1498='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_21368, c_26109])).
% 10.94/4.90  tff(c_21350, plain, (![A_1224]: (k3_xboole_0(A_1224, A_1224)=A_1224)), inference(resolution, [status(thm)], [c_21346, c_34])).
% 10.94/4.90  tff(c_22022, plain, (![B_1296, D_1294, A_1293, E_1297, C_1295]: (r2_hidden('#skF_4'(A_1293, D_1294, C_1295, B_1296, E_1297), k3_xboole_0(B_1296, D_1294)) | ~r2_hidden(A_1293, k3_xboole_0(k2_zfmisc_1(B_1296, C_1295), k2_zfmisc_1(D_1294, E_1297))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.90  tff(c_22037, plain, (![A_1293, B_1296, C_1295]: (r2_hidden('#skF_4'(A_1293, B_1296, C_1295, B_1296, C_1295), k3_xboole_0(B_1296, B_1296)) | ~r2_hidden(A_1293, k2_zfmisc_1(B_1296, C_1295)))), inference(superposition, [status(thm), theory('equality')], [c_21350, c_22022])).
% 10.94/4.90  tff(c_25758, plain, (![A_1486, B_1487, C_1488]: (r2_hidden('#skF_4'(A_1486, B_1487, C_1488, B_1487, C_1488), B_1487) | ~r2_hidden(A_1486, k2_zfmisc_1(B_1487, C_1488)))), inference(demodulation, [status(thm), theory('equality')], [c_21350, c_22037])).
% 10.94/4.90  tff(c_21405, plain, (![A_1231]: (k4_xboole_0(A_1231, A_1231)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14834, c_21360])).
% 10.94/4.90  tff(c_21413, plain, (![D_11, A_1231]: (r2_hidden(D_11, A_1231) | ~r2_hidden(D_11, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_21405, c_12])).
% 10.94/4.90  tff(c_25803, plain, (![A_1486, C_1488, A_1231]: (r2_hidden('#skF_4'(A_1486, '#skF_9', C_1488, '#skF_9', C_1488), A_1231) | ~r2_hidden(A_1486, k2_zfmisc_1('#skF_9', C_1488)))), inference(resolution, [status(thm)], [c_25758, c_21413])).
% 10.94/4.90  tff(c_26972, plain, (![A_1531, C_1532, A_1533]: (r2_hidden('#skF_4'(A_1531, '#skF_9', C_1532, '#skF_9', C_1532), A_1533) | ~r2_hidden(A_1531, k2_zfmisc_1('#skF_9', C_1532)))), inference(resolution, [status(thm)], [c_25758, c_21413])).
% 10.94/4.90  tff(c_27364, plain, (![A_1545, C_1546, B_1547]: (~r2_hidden('#skF_4'(A_1545, '#skF_9', C_1546, '#skF_9', C_1546), B_1547) | ~r2_hidden(A_1545, k2_zfmisc_1('#skF_9', C_1546)))), inference(resolution, [status(thm)], [c_26972, c_10])).
% 10.94/4.90  tff(c_27404, plain, (![A_1551, C_1552]: (~r2_hidden(A_1551, k2_zfmisc_1('#skF_9', C_1552)))), inference(resolution, [status(thm)], [c_25803, c_27364])).
% 10.94/4.90  tff(c_27554, plain, (![C_1552]: (k2_zfmisc_1('#skF_9', C_1552)='#skF_9')), inference(resolution, [status(thm)], [c_26167, c_27404])).
% 10.94/4.90  tff(c_14901, plain, (![A_878, B_879]: (~r2_hidden('#skF_1'(A_878, B_879), B_879) | r1_tarski(A_878, B_879))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.90  tff(c_14922, plain, (![A_882]: (r1_tarski(A_882, A_882))), inference(resolution, [status(thm)], [c_6, c_14901])).
% 10.94/4.90  tff(c_14930, plain, (![A_883]: (k3_xboole_0(A_883, A_883)=A_883)), inference(resolution, [status(thm)], [c_14922, c_34])).
% 10.94/4.90  tff(c_14936, plain, (![A_883]: (k5_xboole_0(A_883, A_883)=k4_xboole_0(A_883, A_883))), inference(superposition, [status(thm), theory('equality')], [c_14930, c_30])).
% 10.94/4.90  tff(c_14944, plain, (![A_883]: (k4_xboole_0(A_883, A_883)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14834, c_14936])).
% 10.94/4.90  tff(c_14976, plain, (![D_886, A_887, B_888]: (r2_hidden(D_886, A_887) | ~r2_hidden(D_886, k4_xboole_0(A_887, B_888)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_15840, plain, (![A_981, B_982, B_983]: (r2_hidden('#skF_1'(k4_xboole_0(A_981, B_982), B_983), A_981) | r1_tarski(k4_xboole_0(A_981, B_982), B_983))), inference(resolution, [status(thm)], [c_6, c_14976])).
% 10.94/4.90  tff(c_15963, plain, (![A_987, B_988]: (r1_tarski(k4_xboole_0(A_987, B_988), A_987))), inference(resolution, [status(thm)], [c_15840, c_4])).
% 10.94/4.90  tff(c_15987, plain, (![A_989, B_990]: (k3_xboole_0(k4_xboole_0(A_989, B_990), A_989)=k4_xboole_0(A_989, B_990))), inference(resolution, [status(thm)], [c_15963, c_34])).
% 10.94/4.90  tff(c_16018, plain, (![A_989, B_990]: (k5_xboole_0(k4_xboole_0(A_989, B_990), k4_xboole_0(A_989, B_990))=k4_xboole_0(k4_xboole_0(A_989, B_990), A_989))), inference(superposition, [status(thm), theory('equality')], [c_15987, c_30])).
% 10.94/4.90  tff(c_16041, plain, (![A_989, B_990]: (k4_xboole_0(k4_xboole_0(A_989, B_990), A_989)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14834, c_16018])).
% 10.94/4.90  tff(c_15502, plain, (![A_943, B_944, C_945]: (r2_hidden('#skF_2'(A_943, B_944, C_945), A_943) | r2_hidden('#skF_3'(A_943, B_944, C_945), C_945) | k4_xboole_0(A_943, B_944)=C_945)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.90  tff(c_19618, plain, (![A_1156, B_1157, B_1158, C_1159]: (r2_hidden('#skF_2'(k4_xboole_0(A_1156, B_1157), B_1158, C_1159), A_1156) | r2_hidden('#skF_3'(k4_xboole_0(A_1156, B_1157), B_1158, C_1159), C_1159) | k4_xboole_0(k4_xboole_0(A_1156, B_1157), B_1158)=C_1159)), inference(resolution, [status(thm)], [c_15502, c_12])).
% 10.94/4.90  tff(c_19651, plain, (![A_1156, B_1157, C_1159]: (r2_hidden('#skF_3'(k4_xboole_0(A_1156, B_1157), A_1156, C_1159), C_1159) | k4_xboole_0(k4_xboole_0(A_1156, B_1157), A_1156)=C_1159)), inference(resolution, [status(thm)], [c_19618, c_22])).
% 10.94/4.90  tff(c_19793, plain, (![A_1160, B_1161, C_1162]: (r2_hidden('#skF_3'(k4_xboole_0(A_1160, B_1161), A_1160, C_1162), C_1162) | C_1162='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16041, c_19651])).
% 10.94/4.90  tff(c_19851, plain, (![A_883, C_1162]: (r2_hidden('#skF_3'('#skF_9', A_883, C_1162), C_1162) | C_1162='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_14944, c_19793])).
% 10.94/4.90  tff(c_14926, plain, (![A_882]: (k3_xboole_0(A_882, A_882)=A_882)), inference(resolution, [status(thm)], [c_14922, c_34])).
% 10.94/4.90  tff(c_15746, plain, (![D_966, C_967, A_965, B_968, E_969]: (r2_hidden('#skF_5'(A_965, D_966, C_967, B_968, E_969), k3_xboole_0(C_967, E_969)) | ~r2_hidden(A_965, k3_xboole_0(k2_zfmisc_1(B_968, C_967), k2_zfmisc_1(D_966, E_969))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.91  tff(c_15764, plain, (![A_965, B_968, C_967]: (r2_hidden('#skF_5'(A_965, B_968, C_967, B_968, C_967), k3_xboole_0(C_967, C_967)) | ~r2_hidden(A_965, k2_zfmisc_1(B_968, C_967)))), inference(superposition, [status(thm), theory('equality')], [c_14926, c_15746])).
% 10.94/4.91  tff(c_19348, plain, (![A_1147, B_1148, C_1149]: (r2_hidden('#skF_5'(A_1147, B_1148, C_1149, B_1148, C_1149), C_1149) | ~r2_hidden(A_1147, k2_zfmisc_1(B_1148, C_1149)))), inference(demodulation, [status(thm), theory('equality')], [c_14926, c_15764])).
% 10.94/4.91  tff(c_14982, plain, (![A_889]: (k4_xboole_0(A_889, A_889)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14834, c_14936])).
% 10.94/4.91  tff(c_14987, plain, (![D_11, A_889]: (r2_hidden(D_11, A_889) | ~r2_hidden(D_11, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_14982, c_12])).
% 10.94/4.91  tff(c_19393, plain, (![A_1147, B_1148, A_889]: (r2_hidden('#skF_5'(A_1147, B_1148, '#skF_9', B_1148, '#skF_9'), A_889) | ~r2_hidden(A_1147, k2_zfmisc_1(B_1148, '#skF_9')))), inference(resolution, [status(thm)], [c_19348, c_14987])).
% 10.94/4.91  tff(c_15593, plain, (![E_956, B_955, C_954, A_952, D_953]: (r2_hidden('#skF_4'(A_952, D_953, C_954, B_955, E_956), k3_xboole_0(B_955, D_953)) | ~r2_hidden(A_952, k3_xboole_0(k2_zfmisc_1(B_955, C_954), k2_zfmisc_1(D_953, E_956))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.91  tff(c_15608, plain, (![A_952, B_955, C_954]: (r2_hidden('#skF_4'(A_952, B_955, C_954, B_955, C_954), k3_xboole_0(B_955, B_955)) | ~r2_hidden(A_952, k2_zfmisc_1(B_955, C_954)))), inference(superposition, [status(thm), theory('equality')], [c_14926, c_15593])).
% 10.94/4.91  tff(c_15616, plain, (![A_952, B_955, C_954]: (r2_hidden('#skF_4'(A_952, B_955, C_954, B_955, C_954), B_955) | ~r2_hidden(A_952, k2_zfmisc_1(B_955, C_954)))), inference(demodulation, [status(thm), theory('equality')], [c_14926, c_15608])).
% 10.94/4.91  tff(c_16937, plain, (![A_1061, B_1062, C_1063]: (r2_hidden('#skF_4'(A_1061, B_1062, C_1063, B_1062, C_1063), B_1062) | ~r2_hidden(A_1061, k2_zfmisc_1(B_1062, C_1063)))), inference(demodulation, [status(thm), theory('equality')], [c_14926, c_15608])).
% 10.94/4.91  tff(c_14990, plain, (![D_11, A_889]: (~r2_hidden(D_11, A_889) | ~r2_hidden(D_11, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_14982, c_10])).
% 10.94/4.91  tff(c_20478, plain, (![A_1185, B_1186, C_1187]: (~r2_hidden('#skF_4'(A_1185, B_1186, C_1187, B_1186, C_1187), '#skF_9') | ~r2_hidden(A_1185, k2_zfmisc_1(B_1186, C_1187)))), inference(resolution, [status(thm)], [c_16937, c_14990])).
% 10.94/4.91  tff(c_20484, plain, (![A_1188, C_1189]: (~r2_hidden(A_1188, k2_zfmisc_1('#skF_9', C_1189)))), inference(resolution, [status(thm)], [c_15616, c_20478])).
% 10.94/4.91  tff(c_21087, plain, (![A_1198, B_1199]: (~r2_hidden(A_1198, k2_zfmisc_1(B_1199, '#skF_9')))), inference(resolution, [status(thm)], [c_19393, c_20484])).
% 10.94/4.91  tff(c_21223, plain, (![B_1199]: (k2_zfmisc_1(B_1199, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_19851, c_21087])).
% 10.94/4.91  tff(c_14831, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_52])).
% 10.94/4.91  tff(c_14839, plain, ('#skF_6'='#skF_9' | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_14832, c_14832, c_14831])).
% 10.94/4.91  tff(c_14840, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_14839])).
% 10.94/4.91  tff(c_50, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.94/4.91  tff(c_14854, plain, (k2_zfmisc_1('#skF_6', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_14832, c_14840, c_14832, c_50])).
% 10.94/4.91  tff(c_21254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21223, c_14854])).
% 10.94/4.91  tff(c_21255, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_14839])).
% 10.94/4.91  tff(c_21269, plain, (k2_zfmisc_1('#skF_9', '#skF_7')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_14832, c_21255, c_14832, c_50])).
% 10.94/4.91  tff(c_27585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27554, c_21269])).
% 10.94/4.91  tff(c_27587, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 10.94/4.91  tff(c_27588, plain, (![A_20]: (k5_xboole_0(A_20, A_20)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27587, c_36])).
% 10.94/4.91  tff(c_33427, plain, (![D_1900, A_1901, B_1902]: (r2_hidden(D_1900, A_1901) | ~r2_hidden(D_1900, k4_xboole_0(A_1901, B_1902)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.91  tff(c_34529, plain, (![A_2018, B_2019, B_2020]: (r2_hidden('#skF_1'(k4_xboole_0(A_2018, B_2019), B_2020), A_2018) | r1_tarski(k4_xboole_0(A_2018, B_2019), B_2020))), inference(resolution, [status(thm)], [c_6, c_33427])).
% 10.94/4.91  tff(c_34588, plain, (![A_2021, B_2022]: (r1_tarski(k4_xboole_0(A_2021, B_2022), A_2021))), inference(resolution, [status(thm)], [c_34529, c_4])).
% 10.94/4.91  tff(c_34617, plain, (![A_2023, B_2024]: (k3_xboole_0(k4_xboole_0(A_2023, B_2024), A_2023)=k4_xboole_0(A_2023, B_2024))), inference(resolution, [status(thm)], [c_34588, c_34])).
% 10.94/4.91  tff(c_34648, plain, (![A_2023, B_2024]: (k5_xboole_0(k4_xboole_0(A_2023, B_2024), k4_xboole_0(A_2023, B_2024))=k4_xboole_0(k4_xboole_0(A_2023, B_2024), A_2023))), inference(superposition, [status(thm), theory('equality')], [c_34617, c_30])).
% 10.94/4.91  tff(c_34671, plain, (![A_2023, B_2024]: (k4_xboole_0(k4_xboole_0(A_2023, B_2024), A_2023)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27588, c_34648])).
% 10.94/4.91  tff(c_33901, plain, (![A_1956, B_1957, C_1958]: (r2_hidden('#skF_2'(A_1956, B_1957, C_1958), A_1956) | r2_hidden('#skF_3'(A_1956, B_1957, C_1958), C_1958) | k4_xboole_0(A_1956, B_1957)=C_1958)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.91  tff(c_38206, plain, (![A_2181, B_2182, B_2183, C_2184]: (r2_hidden('#skF_2'(k4_xboole_0(A_2181, B_2182), B_2183, C_2184), A_2181) | r2_hidden('#skF_3'(k4_xboole_0(A_2181, B_2182), B_2183, C_2184), C_2184) | k4_xboole_0(k4_xboole_0(A_2181, B_2182), B_2183)=C_2184)), inference(resolution, [status(thm)], [c_33901, c_12])).
% 10.94/4.91  tff(c_38242, plain, (![A_2181, B_2182, C_2184]: (r2_hidden('#skF_3'(k4_xboole_0(A_2181, B_2182), A_2181, C_2184), C_2184) | k4_xboole_0(k4_xboole_0(A_2181, B_2182), A_2181)=C_2184)), inference(resolution, [status(thm)], [c_38206, c_22])).
% 10.94/4.91  tff(c_38354, plain, (![A_2181, B_2182, C_2184]: (r2_hidden('#skF_3'(k4_xboole_0(A_2181, B_2182), A_2181, C_2184), C_2184) | C_2184='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34671, c_38242])).
% 10.94/4.91  tff(c_33416, plain, (![A_1898, B_1899]: (r2_hidden('#skF_1'(A_1898, B_1899), A_1898) | r1_tarski(A_1898, B_1899))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.91  tff(c_33433, plain, (![A_1903]: (r1_tarski(A_1903, A_1903))), inference(resolution, [status(thm)], [c_33416, c_4])).
% 10.94/4.91  tff(c_33437, plain, (![A_1903]: (k3_xboole_0(A_1903, A_1903)=A_1903)), inference(resolution, [status(thm)], [c_33433, c_34])).
% 10.94/4.91  tff(c_34138, plain, (![A_1974, B_1977, C_1976, E_1978, D_1975]: (r2_hidden('#skF_5'(A_1974, D_1975, C_1976, B_1977, E_1978), k3_xboole_0(C_1976, E_1978)) | ~r2_hidden(A_1974, k3_xboole_0(k2_zfmisc_1(B_1977, C_1976), k2_zfmisc_1(D_1975, E_1978))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.91  tff(c_34153, plain, (![A_1974, B_1977, C_1976]: (r2_hidden('#skF_5'(A_1974, B_1977, C_1976, B_1977, C_1976), k3_xboole_0(C_1976, C_1976)) | ~r2_hidden(A_1974, k2_zfmisc_1(B_1977, C_1976)))), inference(superposition, [status(thm), theory('equality')], [c_33437, c_34138])).
% 10.94/4.91  tff(c_37572, plain, (![A_2150, B_2151, C_2152]: (r2_hidden('#skF_5'(A_2150, B_2151, C_2152, B_2151, C_2152), C_2152) | ~r2_hidden(A_2150, k2_zfmisc_1(B_2151, C_2152)))), inference(demodulation, [status(thm), theory('equality')], [c_33437, c_34153])).
% 10.94/4.91  tff(c_33441, plain, (![A_1904]: (k3_xboole_0(A_1904, A_1904)=A_1904)), inference(resolution, [status(thm)], [c_33433, c_34])).
% 10.94/4.91  tff(c_33447, plain, (![A_1904]: (k5_xboole_0(A_1904, A_1904)=k4_xboole_0(A_1904, A_1904))), inference(superposition, [status(thm), theory('equality')], [c_33441, c_30])).
% 10.94/4.91  tff(c_33492, plain, (![A_1910]: (k4_xboole_0(A_1910, A_1910)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27588, c_33447])).
% 10.94/4.91  tff(c_33497, plain, (![D_11, A_1910]: (r2_hidden(D_11, A_1910) | ~r2_hidden(D_11, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_33492, c_12])).
% 10.94/4.91  tff(c_37617, plain, (![A_2150, B_2151, A_1910]: (r2_hidden('#skF_5'(A_2150, B_2151, '#skF_8', B_2151, '#skF_8'), A_1910) | ~r2_hidden(A_2150, k2_zfmisc_1(B_2151, '#skF_8')))), inference(resolution, [status(thm)], [c_37572, c_33497])).
% 10.94/4.91  tff(c_38003, plain, (![A_2169, B_2170, A_2171]: (r2_hidden('#skF_5'(A_2169, B_2170, '#skF_8', B_2170, '#skF_8'), A_2171) | ~r2_hidden(A_2169, k2_zfmisc_1(B_2170, '#skF_8')))), inference(resolution, [status(thm)], [c_37572, c_33497])).
% 10.94/4.91  tff(c_39610, plain, (![A_2232, B_2233, B_2234]: (~r2_hidden('#skF_5'(A_2232, B_2233, '#skF_8', B_2233, '#skF_8'), B_2234) | ~r2_hidden(A_2232, k2_zfmisc_1(B_2233, '#skF_8')))), inference(resolution, [status(thm)], [c_38003, c_10])).
% 10.94/4.91  tff(c_39630, plain, (![A_2235, B_2236]: (~r2_hidden(A_2235, k2_zfmisc_1(B_2236, '#skF_8')))), inference(resolution, [status(thm)], [c_37617, c_39610])).
% 10.94/4.91  tff(c_39786, plain, (![B_2236]: (k2_zfmisc_1(B_2236, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_38354, c_39630])).
% 10.94/4.91  tff(c_27666, plain, (![A_1569, B_1570]: (~r2_hidden('#skF_1'(A_1569, B_1570), B_1570) | r1_tarski(A_1569, B_1570))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.94/4.91  tff(c_27672, plain, (![A_1571]: (r1_tarski(A_1571, A_1571))), inference(resolution, [status(thm)], [c_6, c_27666])).
% 10.94/4.91  tff(c_27680, plain, (![A_1572]: (k3_xboole_0(A_1572, A_1572)=A_1572)), inference(resolution, [status(thm)], [c_27672, c_34])).
% 10.94/4.91  tff(c_27686, plain, (![A_1572]: (k5_xboole_0(A_1572, A_1572)=k4_xboole_0(A_1572, A_1572))), inference(superposition, [status(thm), theory('equality')], [c_27680, c_30])).
% 10.94/4.91  tff(c_27694, plain, (![A_1572]: (k4_xboole_0(A_1572, A_1572)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27588, c_27686])).
% 10.94/4.91  tff(c_28251, plain, (![A_1633, B_1634, C_1635]: (r2_hidden('#skF_2'(A_1633, B_1634, C_1635), A_1633) | r2_hidden('#skF_3'(A_1633, B_1634, C_1635), C_1635) | k4_xboole_0(A_1633, B_1634)=C_1635)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.94/4.91  tff(c_28258, plain, (![A_1633, C_1635]: (r2_hidden('#skF_3'(A_1633, A_1633, C_1635), C_1635) | k4_xboole_0(A_1633, A_1633)=C_1635)), inference(resolution, [status(thm)], [c_28251, c_22])).
% 10.94/4.91  tff(c_28289, plain, (![A_1633, C_1635]: (r2_hidden('#skF_3'(A_1633, A_1633, C_1635), C_1635) | C_1635='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27694, c_28258])).
% 10.94/4.91  tff(c_27676, plain, (![A_1571]: (k3_xboole_0(A_1571, A_1571)=A_1571)), inference(resolution, [status(thm)], [c_27672, c_34])).
% 10.94/4.91  tff(c_28487, plain, (![E_1660, B_1659, C_1658, A_1656, D_1657]: (r2_hidden('#skF_4'(A_1656, D_1657, C_1658, B_1659, E_1660), k3_xboole_0(B_1659, D_1657)) | ~r2_hidden(A_1656, k3_xboole_0(k2_zfmisc_1(B_1659, C_1658), k2_zfmisc_1(D_1657, E_1660))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.91  tff(c_28505, plain, (![A_1656, B_1659, C_1658]: (r2_hidden('#skF_4'(A_1656, B_1659, C_1658, B_1659, C_1658), k3_xboole_0(B_1659, B_1659)) | ~r2_hidden(A_1656, k2_zfmisc_1(B_1659, C_1658)))), inference(superposition, [status(thm), theory('equality')], [c_27676, c_28487])).
% 10.94/4.91  tff(c_29751, plain, (![A_1752, B_1753, C_1754]: (r2_hidden('#skF_4'(A_1752, B_1753, C_1754, B_1753, C_1754), B_1753) | ~r2_hidden(A_1752, k2_zfmisc_1(B_1753, C_1754)))), inference(demodulation, [status(thm), theory('equality')], [c_27676, c_28505])).
% 10.94/4.91  tff(c_27739, plain, (![A_1581]: (k4_xboole_0(A_1581, A_1581)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27588, c_27686])).
% 10.94/4.91  tff(c_27747, plain, (![D_11, A_1581]: (r2_hidden(D_11, A_1581) | ~r2_hidden(D_11, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_27739, c_12])).
% 10.94/4.91  tff(c_29785, plain, (![A_1752, C_1754, A_1581]: (r2_hidden('#skF_4'(A_1752, '#skF_8', C_1754, '#skF_8', C_1754), A_1581) | ~r2_hidden(A_1752, k2_zfmisc_1('#skF_8', C_1754)))), inference(resolution, [status(thm)], [c_29751, c_27747])).
% 10.94/4.91  tff(c_28377, plain, (![C_1646, E_1648, B_1647, D_1645, A_1644]: (r2_hidden('#skF_5'(A_1644, D_1645, C_1646, B_1647, E_1648), k3_xboole_0(C_1646, E_1648)) | ~r2_hidden(A_1644, k3_xboole_0(k2_zfmisc_1(B_1647, C_1646), k2_zfmisc_1(D_1645, E_1648))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.94/4.91  tff(c_28392, plain, (![A_1644, B_1647, C_1646]: (r2_hidden('#skF_5'(A_1644, B_1647, C_1646, B_1647, C_1646), k3_xboole_0(C_1646, C_1646)) | ~r2_hidden(A_1644, k2_zfmisc_1(B_1647, C_1646)))), inference(superposition, [status(thm), theory('equality')], [c_27676, c_28377])).
% 10.94/4.91  tff(c_28400, plain, (![A_1644, B_1647, C_1646]: (r2_hidden('#skF_5'(A_1644, B_1647, C_1646, B_1647, C_1646), C_1646) | ~r2_hidden(A_1644, k2_zfmisc_1(B_1647, C_1646)))), inference(demodulation, [status(thm), theory('equality')], [c_27676, c_28392])).
% 10.94/4.91  tff(c_29713, plain, (![A_1749, B_1750, C_1751]: (r2_hidden('#skF_5'(A_1749, B_1750, C_1751, B_1750, C_1751), C_1751) | ~r2_hidden(A_1749, k2_zfmisc_1(B_1750, C_1751)))), inference(demodulation, [status(thm), theory('equality')], [c_27676, c_28392])).
% 10.94/4.91  tff(c_27744, plain, (![D_11, A_1581]: (~r2_hidden(D_11, A_1581) | ~r2_hidden(D_11, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_27739, c_10])).
% 10.94/4.91  tff(c_32874, plain, (![A_1867, B_1868, C_1869]: (~r2_hidden('#skF_5'(A_1867, B_1868, C_1869, B_1868, C_1869), '#skF_8') | ~r2_hidden(A_1867, k2_zfmisc_1(B_1868, C_1869)))), inference(resolution, [status(thm)], [c_29713, c_27744])).
% 10.94/4.91  tff(c_32880, plain, (![A_1870, B_1871]: (~r2_hidden(A_1870, k2_zfmisc_1(B_1871, '#skF_8')))), inference(resolution, [status(thm)], [c_28400, c_32874])).
% 10.94/4.91  tff(c_33179, plain, (![A_1874, C_1875]: (~r2_hidden(A_1874, k2_zfmisc_1('#skF_8', C_1875)))), inference(resolution, [status(thm)], [c_29785, c_32880])).
% 10.94/4.91  tff(c_33306, plain, (![C_1875]: (k2_zfmisc_1('#skF_8', C_1875)='#skF_8')), inference(resolution, [status(thm)], [c_28289, c_33179])).
% 10.94/4.91  tff(c_56, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.94/4.91  tff(c_27602, plain, ('#skF_7'='#skF_8' | '#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_27587, c_27587, c_27587, c_56])).
% 10.94/4.91  tff(c_27603, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_27602])).
% 10.94/4.91  tff(c_27586, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 10.94/4.91  tff(c_27593, plain, (k2_zfmisc_1('#skF_6', '#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_27587, c_27586])).
% 10.94/4.91  tff(c_27604, plain, (k2_zfmisc_1('#skF_8', '#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_27603, c_27593])).
% 10.94/4.91  tff(c_33348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33306, c_27604])).
% 10.94/4.91  tff(c_33349, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_27602])).
% 10.94/4.91  tff(c_33351, plain, (k2_zfmisc_1('#skF_6', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_33349, c_27593])).
% 10.94/4.91  tff(c_39817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39786, c_33351])).
% 10.94/4.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/4.91  
% 10.94/4.91  Inference rules
% 10.94/4.91  ----------------------
% 10.94/4.91  #Ref     : 0
% 10.94/4.91  #Sup     : 9135
% 10.94/4.91  #Fact    : 0
% 10.94/4.91  #Define  : 0
% 10.94/4.91  #Split   : 9
% 10.94/4.91  #Chain   : 0
% 10.94/4.91  #Close   : 0
% 10.94/4.91  
% 10.94/4.91  Ordering : KBO
% 10.94/4.91  
% 10.94/4.91  Simplification rules
% 10.94/4.91  ----------------------
% 10.94/4.91  #Subsume      : 1674
% 10.94/4.91  #Demod        : 8339
% 10.94/4.91  #Tautology    : 3735
% 10.94/4.91  #SimpNegUnit  : 12
% 10.94/4.91  #BackRed      : 91
% 10.94/4.91  
% 10.94/4.91  #Partial instantiations: 0
% 10.94/4.91  #Strategies tried      : 1
% 10.94/4.91  
% 10.94/4.91  Timing (in seconds)
% 10.94/4.91  ----------------------
% 10.94/4.91  Preprocessing        : 0.31
% 10.94/4.91  Parsing              : 0.16
% 10.94/4.91  CNF conversion       : 0.02
% 10.94/4.91  Main loop            : 3.75
% 10.94/4.91  Inferencing          : 1.12
% 10.94/4.91  Reduction            : 1.28
% 10.94/4.91  Demodulation         : 0.98
% 10.94/4.91  BG Simplification    : 0.13
% 10.94/4.91  Subsumption          : 0.94
% 10.94/4.91  Abstraction          : 0.20
% 10.94/4.91  MUC search           : 0.00
% 10.94/4.91  Cooper               : 0.00
% 10.94/4.91  Total                : 4.14
% 10.94/4.91  Index Insertion      : 0.00
% 10.94/4.91  Index Deletion       : 0.00
% 10.94/4.91  Index Matching       : 0.00
% 10.94/4.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
