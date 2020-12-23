%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:58 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 454 expanded)
%              Number of leaves         :   27 ( 157 expanded)
%              Depth                    :   12
%              Number of atoms          :  142 ( 850 expanded)
%              Number of equality atoms :   40 ( 198 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_50,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_61,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [D_57,B_58,A_59] :
      ( ~ r2_hidden(D_57,B_58)
      | ~ r2_hidden(D_57,k4_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [D_60,A_61] :
      ( ~ r2_hidden(D_60,k1_xboole_0)
      | ~ r2_hidden(D_60,A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_76])).

tff(c_89,plain,(
    ! [A_61] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),A_61)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_92,plain,(
    ! [A_65] : ~ r2_hidden('#skF_1'(k1_xboole_0),A_65) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_97,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_92])).

tff(c_1034,plain,(
    ! [A_163,B_164] :
      ( r2_hidden(k4_tarski('#skF_4'(A_163,B_164),'#skF_5'(A_163,B_164)),A_163)
      | r2_hidden('#skF_6'(A_163,B_164),B_164)
      | k1_relat_1(A_163) = B_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3922,plain,(
    ! [A_249,B_250] :
      ( ~ v1_xboole_0(A_249)
      | r2_hidden('#skF_6'(A_249,B_250),B_250)
      | k1_relat_1(A_249) = B_250 ) ),
    inference(resolution,[status(thm)],[c_1034,c_2])).

tff(c_1190,plain,(
    ! [A_170,B_171] :
      ( r2_hidden(k4_tarski('#skF_9'(A_170,B_171),'#skF_8'(A_170,B_171)),A_170)
      | r2_hidden('#skF_10'(A_170,B_171),B_171)
      | k2_relat_1(A_170) = B_171 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2383,plain,(
    ! [A_235,B_236] :
      ( ~ v1_xboole_0(A_235)
      | r2_hidden('#skF_10'(A_235,B_236),B_236)
      | k2_relat_1(A_235) = B_236 ) ),
    inference(resolution,[status(thm)],[c_1190,c_2])).

tff(c_2546,plain,(
    ! [B_237,A_238] :
      ( ~ v1_xboole_0(B_237)
      | ~ v1_xboole_0(A_238)
      | k2_relat_1(A_238) = B_237 ) ),
    inference(resolution,[status(thm)],[c_2383,c_2])).

tff(c_2676,plain,(
    ! [A_239] :
      ( ~ v1_xboole_0(A_239)
      | k2_relat_1(A_239) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_97,c_2546])).

tff(c_2848,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_2676])).

tff(c_38,plain,(
    ! [A_31,C_46] :
      ( r2_hidden(k4_tarski('#skF_11'(A_31,k2_relat_1(A_31),C_46),C_46),A_31)
      | ~ r2_hidden(C_46,k2_relat_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_406,plain,(
    ! [A_108,C_109] :
      ( r2_hidden(k4_tarski('#skF_11'(A_108,k2_relat_1(A_108),C_109),C_109),A_108)
      | ~ r2_hidden(C_109,k2_relat_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_453,plain,(
    ! [A_110,C_111] :
      ( ~ v1_xboole_0(A_110)
      | ~ r2_hidden(C_111,k2_relat_1(A_110)) ) ),
    inference(resolution,[status(thm)],[c_406,c_2])).

tff(c_550,plain,(
    ! [A_121,C_122] :
      ( ~ v1_xboole_0(A_121)
      | ~ r2_hidden(C_122,k2_relat_1(k2_relat_1(A_121))) ) ),
    inference(resolution,[status(thm)],[c_38,c_453])).

tff(c_950,plain,(
    ! [A_157,C_158] :
      ( ~ v1_xboole_0(A_157)
      | ~ r2_hidden(C_158,k2_relat_1(k2_relat_1(k2_relat_1(A_157)))) ) ),
    inference(resolution,[status(thm)],[c_38,c_550])).

tff(c_985,plain,(
    ! [A_157,C_46] :
      ( ~ v1_xboole_0(A_157)
      | ~ r2_hidden(C_46,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_157))))) ) ),
    inference(resolution,[status(thm)],[c_38,c_950])).

tff(c_2876,plain,(
    ! [C_46] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_46,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2848,c_985])).

tff(c_2965,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_2848,c_2848,c_97,c_2876])).

tff(c_4193,plain,(
    ! [A_253] :
      ( ~ v1_xboole_0(A_253)
      | k1_relat_1(A_253) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3922,c_2965])).

tff(c_4331,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_4193])).

tff(c_4380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_4331])).

tff(c_4381,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_4665,plain,(
    ! [C_293,A_294] :
      ( r2_hidden(k4_tarski(C_293,'#skF_7'(A_294,k1_relat_1(A_294),C_293)),A_294)
      | ~ r2_hidden(C_293,k1_relat_1(A_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4711,plain,(
    ! [A_295,C_296] :
      ( ~ v1_xboole_0(A_295)
      | ~ r2_hidden(C_296,k1_relat_1(A_295)) ) ),
    inference(resolution,[status(thm)],[c_4665,c_2])).

tff(c_4741,plain,(
    ! [A_295] :
      ( ~ v1_xboole_0(A_295)
      | v1_xboole_0(k1_relat_1(A_295)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4711])).

tff(c_5005,plain,(
    ! [A_336,B_337,C_338] :
      ( r2_hidden('#skF_2'(A_336,B_337,C_338),A_336)
      | r2_hidden('#skF_3'(A_336,B_337,C_338),C_338)
      | k4_xboole_0(A_336,B_337) = C_338 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7127,plain,(
    ! [A_432,C_433] :
      ( r2_hidden('#skF_3'(A_432,A_432,C_433),C_433)
      | k4_xboole_0(A_432,A_432) = C_433 ) ),
    inference(resolution,[status(thm)],[c_5005,c_20])).

tff(c_7285,plain,(
    ! [C_434,A_435] :
      ( ~ v1_xboole_0(C_434)
      | k4_xboole_0(A_435,A_435) = C_434 ) ),
    inference(resolution,[status(thm)],[c_7127,c_2])).

tff(c_7405,plain,(
    ! [A_435] : k4_xboole_0(A_435,A_435) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4381,c_7285])).

tff(c_7284,plain,(
    ! [C_433,A_432] :
      ( ~ v1_xboole_0(C_433)
      | k4_xboole_0(A_432,A_432) = C_433 ) ),
    inference(resolution,[status(thm)],[c_7127,c_2])).

tff(c_7518,plain,(
    ! [C_437] :
      ( ~ v1_xboole_0(C_437)
      | k1_xboole_0 = C_437 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7405,c_7284])).

tff(c_7677,plain,(
    ! [A_438] :
      ( k1_relat_1(A_438) = k1_xboole_0
      | ~ v1_xboole_0(A_438) ) ),
    inference(resolution,[status(thm)],[c_4741,c_7518])).

tff(c_7794,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4381,c_7677])).

tff(c_7836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_7794])).

tff(c_7837,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_10421,plain,(
    ! [A_634,B_635,C_636] :
      ( r2_hidden('#skF_2'(A_634,B_635,C_636),A_634)
      | r2_hidden('#skF_3'(A_634,B_635,C_636),C_636)
      | k4_xboole_0(A_634,B_635) = C_636 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8985,plain,(
    ! [A_545,B_546,C_547] :
      ( r2_hidden('#skF_2'(A_545,B_546,C_547),A_545)
      | r2_hidden('#skF_3'(A_545,B_546,C_547),C_547)
      | k4_xboole_0(A_545,B_546) = C_547 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7857,plain,(
    ! [D_443,B_444,A_445] :
      ( ~ r2_hidden(D_443,B_444)
      | ~ r2_hidden(D_443,k4_xboole_0(A_445,B_444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7866,plain,(
    ! [D_446,A_447] :
      ( ~ r2_hidden(D_446,k1_xboole_0)
      | ~ r2_hidden(D_446,A_447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7857])).

tff(c_7870,plain,(
    ! [A_447] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),A_447)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_7866])).

tff(c_7872,plain,(
    ! [A_448] : ~ r2_hidden('#skF_1'(k1_xboole_0),A_448) ),
    inference(splitLeft,[status(thm)],[c_7870])).

tff(c_7877,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_7872])).

tff(c_7838,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_7978,plain,(
    ! [C_467,A_468] :
      ( r2_hidden(k4_tarski(C_467,'#skF_7'(A_468,k1_relat_1(A_468),C_467)),A_468)
      | ~ r2_hidden(C_467,k1_relat_1(A_468)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8010,plain,(
    ! [A_469,C_470] :
      ( ~ v1_xboole_0(A_469)
      | ~ r2_hidden(C_470,k1_relat_1(A_469)) ) ),
    inference(resolution,[status(thm)],[c_7978,c_2])).

tff(c_8025,plain,(
    ! [C_470] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_470,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7838,c_8010])).

tff(c_8030,plain,(
    ! [C_470] : ~ r2_hidden(C_470,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7877,c_8025])).

tff(c_9300,plain,(
    ! [B_550,C_551] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_550,C_551),C_551)
      | k4_xboole_0(k1_xboole_0,B_550) = C_551 ) ),
    inference(resolution,[status(thm)],[c_8985,c_8030])).

tff(c_9430,plain,(
    ! [B_550] : k4_xboole_0(k1_xboole_0,B_550) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9300,c_8030])).

tff(c_8308,plain,(
    ! [A_498,C_499] :
      ( r2_hidden(k4_tarski('#skF_11'(A_498,k2_relat_1(A_498),C_499),C_499),A_498)
      | ~ r2_hidden(C_499,k2_relat_1(A_498)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8354,plain,(
    ! [C_499] : ~ r2_hidden(C_499,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_8308,c_8030])).

tff(c_9425,plain,(
    ! [B_550] : k4_xboole_0(k1_xboole_0,B_550) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9300,c_8354])).

tff(c_9488,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9430,c_9425])).

tff(c_9489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7837,c_9488])).

tff(c_9490,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7870])).

tff(c_9712,plain,(
    ! [C_584,A_585] :
      ( r2_hidden(k4_tarski(C_584,'#skF_7'(A_585,k1_relat_1(A_585),C_584)),A_585)
      | ~ r2_hidden(C_584,k1_relat_1(A_585)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9755,plain,(
    ! [A_587,C_588] :
      ( ~ v1_xboole_0(A_587)
      | ~ r2_hidden(C_588,k1_relat_1(A_587)) ) ),
    inference(resolution,[status(thm)],[c_9712,c_2])).

tff(c_9782,plain,(
    ! [C_588] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_588,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7838,c_9755])).

tff(c_9790,plain,(
    ! [C_588] : ~ r2_hidden(C_588,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9490,c_9782])).

tff(c_10687,plain,(
    ! [B_638,C_639] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_638,C_639),C_639)
      | k4_xboole_0(k1_xboole_0,B_638) = C_639 ) ),
    inference(resolution,[status(thm)],[c_10421,c_9790])).

tff(c_10796,plain,(
    ! [B_638] : k4_xboole_0(k1_xboole_0,B_638) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10687,c_9790])).

tff(c_9791,plain,(
    ! [C_589] : ~ r2_hidden(C_589,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9490,c_9782])).

tff(c_9818,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_38,c_9791])).

tff(c_10795,plain,(
    ! [B_638] : k4_xboole_0(k1_xboole_0,B_638) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10687,c_9818])).

tff(c_10855,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10796,c_10795])).

tff(c_10856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7837,c_10855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.81/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.66  
% 8.08/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.66  %$ r2_hidden > v1_xboole_0 > k4_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_4
% 8.08/2.66  
% 8.08/2.66  %Foreground sorts:
% 8.08/2.66  
% 8.08/2.66  
% 8.08/2.66  %Background operators:
% 8.08/2.66  
% 8.08/2.66  
% 8.08/2.66  %Foreground operators:
% 8.08/2.66  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.08/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.08/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.08/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.08/2.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.08/2.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.08/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.08/2.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.08/2.66  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 8.08/2.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.08/2.66  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.08/2.66  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 8.08/2.66  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.08/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.08/2.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.08/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.08/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.08/2.66  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.08/2.66  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.08/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.08/2.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.08/2.66  
% 8.08/2.68  tff(f_63, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.08/2.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.08/2.68  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.08/2.68  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.08/2.68  tff(f_51, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 8.08/2.68  tff(f_59, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 8.08/2.68  tff(c_50, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.08/2.68  tff(c_61, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 8.08/2.68  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.08/2.68  tff(c_24, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.08/2.68  tff(c_76, plain, (![D_57, B_58, A_59]: (~r2_hidden(D_57, B_58) | ~r2_hidden(D_57, k4_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.68  tff(c_85, plain, (![D_60, A_61]: (~r2_hidden(D_60, k1_xboole_0) | ~r2_hidden(D_60, A_61))), inference(superposition, [status(thm), theory('equality')], [c_24, c_76])).
% 8.08/2.68  tff(c_89, plain, (![A_61]: (~r2_hidden('#skF_1'(k1_xboole_0), A_61) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_85])).
% 8.08/2.68  tff(c_92, plain, (![A_65]: (~r2_hidden('#skF_1'(k1_xboole_0), A_65))), inference(splitLeft, [status(thm)], [c_89])).
% 8.08/2.68  tff(c_97, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_92])).
% 8.08/2.68  tff(c_1034, plain, (![A_163, B_164]: (r2_hidden(k4_tarski('#skF_4'(A_163, B_164), '#skF_5'(A_163, B_164)), A_163) | r2_hidden('#skF_6'(A_163, B_164), B_164) | k1_relat_1(A_163)=B_164)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.08/2.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.08/2.68  tff(c_3922, plain, (![A_249, B_250]: (~v1_xboole_0(A_249) | r2_hidden('#skF_6'(A_249, B_250), B_250) | k1_relat_1(A_249)=B_250)), inference(resolution, [status(thm)], [c_1034, c_2])).
% 8.08/2.68  tff(c_1190, plain, (![A_170, B_171]: (r2_hidden(k4_tarski('#skF_9'(A_170, B_171), '#skF_8'(A_170, B_171)), A_170) | r2_hidden('#skF_10'(A_170, B_171), B_171) | k2_relat_1(A_170)=B_171)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.08/2.68  tff(c_2383, plain, (![A_235, B_236]: (~v1_xboole_0(A_235) | r2_hidden('#skF_10'(A_235, B_236), B_236) | k2_relat_1(A_235)=B_236)), inference(resolution, [status(thm)], [c_1190, c_2])).
% 8.08/2.68  tff(c_2546, plain, (![B_237, A_238]: (~v1_xboole_0(B_237) | ~v1_xboole_0(A_238) | k2_relat_1(A_238)=B_237)), inference(resolution, [status(thm)], [c_2383, c_2])).
% 8.08/2.68  tff(c_2676, plain, (![A_239]: (~v1_xboole_0(A_239) | k2_relat_1(A_239)=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_2546])).
% 8.08/2.68  tff(c_2848, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_97, c_2676])).
% 8.08/2.68  tff(c_38, plain, (![A_31, C_46]: (r2_hidden(k4_tarski('#skF_11'(A_31, k2_relat_1(A_31), C_46), C_46), A_31) | ~r2_hidden(C_46, k2_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.08/2.68  tff(c_406, plain, (![A_108, C_109]: (r2_hidden(k4_tarski('#skF_11'(A_108, k2_relat_1(A_108), C_109), C_109), A_108) | ~r2_hidden(C_109, k2_relat_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.08/2.68  tff(c_453, plain, (![A_110, C_111]: (~v1_xboole_0(A_110) | ~r2_hidden(C_111, k2_relat_1(A_110)))), inference(resolution, [status(thm)], [c_406, c_2])).
% 8.08/2.68  tff(c_550, plain, (![A_121, C_122]: (~v1_xboole_0(A_121) | ~r2_hidden(C_122, k2_relat_1(k2_relat_1(A_121))))), inference(resolution, [status(thm)], [c_38, c_453])).
% 8.08/2.68  tff(c_950, plain, (![A_157, C_158]: (~v1_xboole_0(A_157) | ~r2_hidden(C_158, k2_relat_1(k2_relat_1(k2_relat_1(A_157)))))), inference(resolution, [status(thm)], [c_38, c_550])).
% 8.08/2.68  tff(c_985, plain, (![A_157, C_46]: (~v1_xboole_0(A_157) | ~r2_hidden(C_46, k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_157))))))), inference(resolution, [status(thm)], [c_38, c_950])).
% 8.08/2.68  tff(c_2876, plain, (![C_46]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_46, k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))), inference(superposition, [status(thm), theory('equality')], [c_2848, c_985])).
% 8.08/2.68  tff(c_2965, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2848, c_2848, c_2848, c_97, c_2876])).
% 8.08/2.68  tff(c_4193, plain, (![A_253]: (~v1_xboole_0(A_253) | k1_relat_1(A_253)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3922, c_2965])).
% 8.08/2.68  tff(c_4331, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_97, c_4193])).
% 8.08/2.68  tff(c_4380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_4331])).
% 8.08/2.68  tff(c_4381, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_89])).
% 8.08/2.68  tff(c_4665, plain, (![C_293, A_294]: (r2_hidden(k4_tarski(C_293, '#skF_7'(A_294, k1_relat_1(A_294), C_293)), A_294) | ~r2_hidden(C_293, k1_relat_1(A_294)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.08/2.68  tff(c_4711, plain, (![A_295, C_296]: (~v1_xboole_0(A_295) | ~r2_hidden(C_296, k1_relat_1(A_295)))), inference(resolution, [status(thm)], [c_4665, c_2])).
% 8.08/2.68  tff(c_4741, plain, (![A_295]: (~v1_xboole_0(A_295) | v1_xboole_0(k1_relat_1(A_295)))), inference(resolution, [status(thm)], [c_4, c_4711])).
% 8.08/2.68  tff(c_5005, plain, (![A_336, B_337, C_338]: (r2_hidden('#skF_2'(A_336, B_337, C_338), A_336) | r2_hidden('#skF_3'(A_336, B_337, C_338), C_338) | k4_xboole_0(A_336, B_337)=C_338)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.68  tff(c_20, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.68  tff(c_7127, plain, (![A_432, C_433]: (r2_hidden('#skF_3'(A_432, A_432, C_433), C_433) | k4_xboole_0(A_432, A_432)=C_433)), inference(resolution, [status(thm)], [c_5005, c_20])).
% 8.08/2.68  tff(c_7285, plain, (![C_434, A_435]: (~v1_xboole_0(C_434) | k4_xboole_0(A_435, A_435)=C_434)), inference(resolution, [status(thm)], [c_7127, c_2])).
% 8.08/2.68  tff(c_7405, plain, (![A_435]: (k4_xboole_0(A_435, A_435)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4381, c_7285])).
% 8.08/2.68  tff(c_7284, plain, (![C_433, A_432]: (~v1_xboole_0(C_433) | k4_xboole_0(A_432, A_432)=C_433)), inference(resolution, [status(thm)], [c_7127, c_2])).
% 8.08/2.68  tff(c_7518, plain, (![C_437]: (~v1_xboole_0(C_437) | k1_xboole_0=C_437)), inference(demodulation, [status(thm), theory('equality')], [c_7405, c_7284])).
% 8.08/2.68  tff(c_7677, plain, (![A_438]: (k1_relat_1(A_438)=k1_xboole_0 | ~v1_xboole_0(A_438))), inference(resolution, [status(thm)], [c_4741, c_7518])).
% 8.08/2.68  tff(c_7794, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4381, c_7677])).
% 8.08/2.68  tff(c_7836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_7794])).
% 8.08/2.68  tff(c_7837, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 8.08/2.68  tff(c_10421, plain, (![A_634, B_635, C_636]: (r2_hidden('#skF_2'(A_634, B_635, C_636), A_634) | r2_hidden('#skF_3'(A_634, B_635, C_636), C_636) | k4_xboole_0(A_634, B_635)=C_636)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.68  tff(c_8985, plain, (![A_545, B_546, C_547]: (r2_hidden('#skF_2'(A_545, B_546, C_547), A_545) | r2_hidden('#skF_3'(A_545, B_546, C_547), C_547) | k4_xboole_0(A_545, B_546)=C_547)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.68  tff(c_7857, plain, (![D_443, B_444, A_445]: (~r2_hidden(D_443, B_444) | ~r2_hidden(D_443, k4_xboole_0(A_445, B_444)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.68  tff(c_7866, plain, (![D_446, A_447]: (~r2_hidden(D_446, k1_xboole_0) | ~r2_hidden(D_446, A_447))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7857])).
% 8.08/2.68  tff(c_7870, plain, (![A_447]: (~r2_hidden('#skF_1'(k1_xboole_0), A_447) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_7866])).
% 8.08/2.68  tff(c_7872, plain, (![A_448]: (~r2_hidden('#skF_1'(k1_xboole_0), A_448))), inference(splitLeft, [status(thm)], [c_7870])).
% 8.08/2.68  tff(c_7877, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_7872])).
% 8.08/2.68  tff(c_7838, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 8.08/2.68  tff(c_7978, plain, (![C_467, A_468]: (r2_hidden(k4_tarski(C_467, '#skF_7'(A_468, k1_relat_1(A_468), C_467)), A_468) | ~r2_hidden(C_467, k1_relat_1(A_468)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.08/2.68  tff(c_8010, plain, (![A_469, C_470]: (~v1_xboole_0(A_469) | ~r2_hidden(C_470, k1_relat_1(A_469)))), inference(resolution, [status(thm)], [c_7978, c_2])).
% 8.08/2.68  tff(c_8025, plain, (![C_470]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_470, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7838, c_8010])).
% 8.08/2.68  tff(c_8030, plain, (![C_470]: (~r2_hidden(C_470, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_7877, c_8025])).
% 8.08/2.68  tff(c_9300, plain, (![B_550, C_551]: (r2_hidden('#skF_3'(k1_xboole_0, B_550, C_551), C_551) | k4_xboole_0(k1_xboole_0, B_550)=C_551)), inference(resolution, [status(thm)], [c_8985, c_8030])).
% 8.08/2.68  tff(c_9430, plain, (![B_550]: (k4_xboole_0(k1_xboole_0, B_550)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9300, c_8030])).
% 8.08/2.68  tff(c_8308, plain, (![A_498, C_499]: (r2_hidden(k4_tarski('#skF_11'(A_498, k2_relat_1(A_498), C_499), C_499), A_498) | ~r2_hidden(C_499, k2_relat_1(A_498)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.08/2.68  tff(c_8354, plain, (![C_499]: (~r2_hidden(C_499, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_8308, c_8030])).
% 8.08/2.68  tff(c_9425, plain, (![B_550]: (k4_xboole_0(k1_xboole_0, B_550)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_9300, c_8354])).
% 8.08/2.68  tff(c_9488, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9430, c_9425])).
% 8.08/2.68  tff(c_9489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7837, c_9488])).
% 8.08/2.68  tff(c_9490, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_7870])).
% 8.08/2.68  tff(c_9712, plain, (![C_584, A_585]: (r2_hidden(k4_tarski(C_584, '#skF_7'(A_585, k1_relat_1(A_585), C_584)), A_585) | ~r2_hidden(C_584, k1_relat_1(A_585)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.08/2.68  tff(c_9755, plain, (![A_587, C_588]: (~v1_xboole_0(A_587) | ~r2_hidden(C_588, k1_relat_1(A_587)))), inference(resolution, [status(thm)], [c_9712, c_2])).
% 8.08/2.68  tff(c_9782, plain, (![C_588]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_588, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7838, c_9755])).
% 8.08/2.68  tff(c_9790, plain, (![C_588]: (~r2_hidden(C_588, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_9490, c_9782])).
% 8.08/2.68  tff(c_10687, plain, (![B_638, C_639]: (r2_hidden('#skF_3'(k1_xboole_0, B_638, C_639), C_639) | k4_xboole_0(k1_xboole_0, B_638)=C_639)), inference(resolution, [status(thm)], [c_10421, c_9790])).
% 8.08/2.68  tff(c_10796, plain, (![B_638]: (k4_xboole_0(k1_xboole_0, B_638)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10687, c_9790])).
% 8.08/2.68  tff(c_9791, plain, (![C_589]: (~r2_hidden(C_589, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_9490, c_9782])).
% 8.08/2.68  tff(c_9818, plain, (![C_46]: (~r2_hidden(C_46, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_38, c_9791])).
% 8.08/2.68  tff(c_10795, plain, (![B_638]: (k4_xboole_0(k1_xboole_0, B_638)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10687, c_9818])).
% 8.08/2.68  tff(c_10855, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10796, c_10795])).
% 8.08/2.68  tff(c_10856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7837, c_10855])).
% 8.08/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.68  
% 8.08/2.68  Inference rules
% 8.08/2.68  ----------------------
% 8.08/2.68  #Ref     : 0
% 8.08/2.68  #Sup     : 2270
% 8.08/2.68  #Fact    : 0
% 8.08/2.68  #Define  : 0
% 8.08/2.68  #Split   : 3
% 8.08/2.68  #Chain   : 0
% 8.08/2.68  #Close   : 0
% 8.08/2.68  
% 8.08/2.68  Ordering : KBO
% 8.08/2.68  
% 8.08/2.68  Simplification rules
% 8.08/2.68  ----------------------
% 8.08/2.68  #Subsume      : 462
% 8.08/2.68  #Demod        : 438
% 8.08/2.68  #Tautology    : 250
% 8.08/2.68  #SimpNegUnit  : 22
% 8.08/2.68  #BackRed      : 13
% 8.08/2.68  
% 8.08/2.68  #Partial instantiations: 0
% 8.08/2.68  #Strategies tried      : 1
% 8.08/2.68  
% 8.08/2.68  Timing (in seconds)
% 8.08/2.68  ----------------------
% 8.08/2.68  Preprocessing        : 0.29
% 8.08/2.68  Parsing              : 0.15
% 8.08/2.68  CNF conversion       : 0.03
% 8.08/2.68  Main loop            : 1.63
% 8.08/2.68  Inferencing          : 0.54
% 8.08/2.68  Reduction            : 0.34
% 8.08/2.68  Demodulation         : 0.22
% 8.08/2.68  BG Simplification    : 0.06
% 8.08/2.68  Subsumption          : 0.56
% 8.08/2.68  Abstraction          : 0.08
% 8.08/2.68  MUC search           : 0.00
% 8.08/2.68  Cooper               : 0.00
% 8.08/2.68  Total                : 1.96
% 8.08/2.68  Index Insertion      : 0.00
% 8.08/2.68  Index Deletion       : 0.00
% 8.08/2.68  Index Matching       : 0.00
% 8.08/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
