%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:59 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 357 expanded)
%              Number of leaves         :   39 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  141 ( 582 expanded)
%              Number of equality atoms :   42 ( 172 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_5 > #skF_1 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_118,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_110,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_70,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_103,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_894,plain,(
    ! [A_183,B_184] :
      ( r2_hidden(k4_tarski('#skF_7'(A_183,B_184),'#skF_6'(A_183,B_184)),A_183)
      | r2_hidden('#skF_8'(A_183,B_184),B_184)
      | k2_relat_1(A_183) = B_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_20,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_340,plain,(
    ! [A_137,C_138,B_139] :
      ( r2_hidden(A_137,C_138)
      | k3_xboole_0(k2_tarski(A_137,B_139),C_138) != k2_tarski(A_137,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_353,plain,(
    ! [A_140,B_141] :
      ( r2_hidden(A_140,k1_xboole_0)
      | k2_tarski(A_140,B_141) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_340])).

tff(c_356,plain,(
    ! [A_142] :
      ( r2_hidden(A_142,k1_xboole_0)
      | k1_tarski(A_142) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_353])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_159,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski(A_94,B_95)
      | ~ r1_tarski(A_94,k3_xboole_0(B_95,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [A_97,A_98] :
      ( r1_tarski(A_97,A_98)
      | ~ r1_tarski(A_97,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_159])).

tff(c_184,plain,(
    ! [A_99,A_100] :
      ( r1_tarski(k1_tarski(A_99),A_100)
      | ~ r2_hidden(A_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_174])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_201,plain,(
    ! [A_99,A_100] :
      ( r2_hidden(A_99,A_100)
      | ~ r2_hidden(A_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_184,c_22])).

tff(c_399,plain,(
    ! [A_145,A_146] :
      ( r2_hidden(A_145,A_146)
      | k1_tarski(A_145) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_356,c_201])).

tff(c_26,plain,(
    ! [A_15,B_16] : ~ r2_hidden(A_15,k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_449,plain,(
    ! [A_145] : k1_tarski(A_145) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_399,c_26])).

tff(c_108,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k1_tarski(A_79),B_80)
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [A_79] :
      ( k1_tarski(A_79) = k1_xboole_0
      | ~ r2_hidden(A_79,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_108,c_12])).

tff(c_450,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_113])).

tff(c_1441,plain,(
    ! [B_209] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_209),B_209)
      | k2_relat_1(k1_xboole_0) = B_209 ) ),
    inference(resolution,[status(thm)],[c_894,c_450])).

tff(c_1612,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1441,c_450])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,A_23)
      | ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( r2_hidden(B_24,A_23)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_469,plain,(
    ! [A_153,C_154] :
      ( r2_hidden(k4_tarski('#skF_9'(A_153,k2_relat_1(A_153),C_154),C_154),A_153)
      | ~ r2_hidden(C_154,k2_relat_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_502,plain,(
    ! [C_155] : ~ r2_hidden(C_155,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_469,c_450])).

tff(c_512,plain,(
    ! [B_24] :
      ( ~ m1_subset_1(B_24,k2_relat_1(k1_xboole_0))
      | v1_xboole_0(k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_34,c_502])).

tff(c_536,plain,(
    ! [B_158] : ~ m1_subset_1(B_158,k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_541,plain,(
    ! [B_24] :
      ( ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_36,c_536])).

tff(c_660,plain,(
    ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_1629,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_660])).

tff(c_1637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1629])).

tff(c_1638,plain,(
    ! [B_24] : ~ v1_xboole_0(B_24) ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_1651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1638,c_2])).

tff(c_1652,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1659,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1652,c_16])).

tff(c_1876,plain,(
    ! [A_233,B_234] :
      ( r2_hidden(k4_tarski('#skF_7'(A_233,B_234),'#skF_6'(A_233,B_234)),A_233)
      | r2_hidden('#skF_8'(A_233,B_234),B_234)
      | k2_relat_1(A_233) = B_234 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1916,plain,(
    ! [B_234] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_234),B_234)
      | k2_relat_1(k1_xboole_0) = B_234 ) ),
    inference(resolution,[status(thm)],[c_1876,c_450])).

tff(c_1955,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_235),B_235)
      | k1_xboole_0 = B_235 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1659,c_1916])).

tff(c_1674,plain,(
    ! [C_213,A_214] :
      ( r2_hidden(k4_tarski(C_213,'#skF_5'(A_214,k1_relat_1(A_214),C_213)),A_214)
      | ~ r2_hidden(C_213,k1_relat_1(A_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1700,plain,(
    ! [C_213] : ~ r2_hidden(C_213,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1674,c_450])).

tff(c_1991,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1955,c_1700])).

tff(c_2022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_1991])).

tff(c_2023,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2024,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2685,plain,(
    ! [A_335,B_336] :
      ( r2_hidden(k4_tarski('#skF_2'(A_335,B_336),'#skF_3'(A_335,B_336)),A_335)
      | r2_hidden('#skF_4'(A_335,B_336),B_336)
      | k1_relat_1(A_335) = B_336 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2253,plain,(
    ! [A_292,C_293,B_294] :
      ( r2_hidden(A_292,C_293)
      | k3_xboole_0(k2_tarski(A_292,B_294),C_293) != k2_tarski(A_292,B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2266,plain,(
    ! [A_295,B_296] :
      ( r2_hidden(A_295,k1_xboole_0)
      | k2_tarski(A_295,B_296) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2253])).

tff(c_2269,plain,(
    ! [A_297] :
      ( r2_hidden(A_297,k1_xboole_0)
      | k1_tarski(A_297) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2266])).

tff(c_2083,plain,(
    ! [A_251,B_252,C_253] :
      ( r1_tarski(A_251,B_252)
      | ~ r1_tarski(A_251,k3_xboole_0(B_252,C_253)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2098,plain,(
    ! [A_254,A_255] :
      ( r1_tarski(A_254,A_255)
      | ~ r1_tarski(A_254,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2083])).

tff(c_2108,plain,(
    ! [A_256,A_257] :
      ( r1_tarski(k1_tarski(A_256),A_257)
      | ~ r2_hidden(A_256,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_2098])).

tff(c_2125,plain,(
    ! [A_256,A_257] :
      ( r2_hidden(A_256,A_257)
      | ~ r2_hidden(A_256,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2108,c_22])).

tff(c_2313,plain,(
    ! [A_300,A_301] :
      ( r2_hidden(A_300,A_301)
      | k1_tarski(A_300) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2269,c_2125])).

tff(c_2353,plain,(
    ! [A_300] : k1_tarski(A_300) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2313,c_26])).

tff(c_2033,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(k1_tarski(A_238),B_239)
      | ~ r2_hidden(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2038,plain,(
    ! [A_238] :
      ( k1_tarski(A_238) = k1_xboole_0
      | ~ r2_hidden(A_238,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2033,c_12])).

tff(c_2354,plain,(
    ! [A_238] : ~ r2_hidden(A_238,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_2353,c_2038])).

tff(c_2745,plain,(
    ! [B_336] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_336),B_336)
      | k1_relat_1(k1_xboole_0) = B_336 ) ),
    inference(resolution,[status(thm)],[c_2685,c_2354])).

tff(c_2779,plain,(
    ! [B_337] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_337),B_337)
      | k1_xboole_0 = B_337 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2024,c_2745])).

tff(c_58,plain,(
    ! [A_50,C_65] :
      ( r2_hidden(k4_tarski('#skF_9'(A_50,k2_relat_1(A_50),C_65),C_65),A_50)
      | ~ r2_hidden(C_65,k2_relat_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2387,plain,(
    ! [A_305] : ~ r2_hidden(A_305,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_2353,c_2038])).

tff(c_2396,plain,(
    ! [C_65] : ~ r2_hidden(C_65,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_58,c_2387])).

tff(c_2835,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2779,c_2396])).

tff(c_2863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2023,c_2835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:50:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.85  
% 4.41/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.85  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_5 > #skF_1 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4
% 4.41/1.85  
% 4.41/1.85  %Foreground sorts:
% 4.41/1.85  
% 4.41/1.85  
% 4.41/1.85  %Background operators:
% 4.41/1.85  
% 4.41/1.85  
% 4.41/1.85  %Foreground operators:
% 4.41/1.85  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.41/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.41/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.41/1.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.41/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.41/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.41/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.41/1.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.41/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.41/1.85  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.41/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.41/1.85  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.41/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.41/1.85  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.41/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.41/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.41/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.41/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.41/1.85  
% 4.58/1.87  tff(f_122, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.58/1.87  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.58/1.87  tff(f_118, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 4.58/1.87  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.58/1.87  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.58/1.87  tff(f_72, axiom, (![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 4.58/1.87  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.58/1.87  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.58/1.87  tff(f_64, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.58/1.87  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.58/1.87  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.58/1.87  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 4.58/1.87  tff(f_110, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 4.58/1.87  tff(c_70, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.58/1.87  tff(c_103, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 4.58/1.87  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.58/1.87  tff(c_894, plain, (![A_183, B_184]: (r2_hidden(k4_tarski('#skF_7'(A_183, B_184), '#skF_6'(A_183, B_184)), A_183) | r2_hidden('#skF_8'(A_183, B_184), B_184) | k2_relat_1(A_183)=B_184)), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.87  tff(c_20, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.58/1.87  tff(c_8, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.58/1.87  tff(c_340, plain, (![A_137, C_138, B_139]: (r2_hidden(A_137, C_138) | k3_xboole_0(k2_tarski(A_137, B_139), C_138)!=k2_tarski(A_137, B_139))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.58/1.87  tff(c_353, plain, (![A_140, B_141]: (r2_hidden(A_140, k1_xboole_0) | k2_tarski(A_140, B_141)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_340])).
% 4.58/1.87  tff(c_356, plain, (![A_142]: (r2_hidden(A_142, k1_xboole_0) | k1_tarski(A_142)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_353])).
% 4.58/1.87  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.58/1.87  tff(c_159, plain, (![A_94, B_95, C_96]: (r1_tarski(A_94, B_95) | ~r1_tarski(A_94, k3_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.58/1.87  tff(c_174, plain, (![A_97, A_98]: (r1_tarski(A_97, A_98) | ~r1_tarski(A_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_159])).
% 4.58/1.87  tff(c_184, plain, (![A_99, A_100]: (r1_tarski(k1_tarski(A_99), A_100) | ~r2_hidden(A_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_174])).
% 4.58/1.87  tff(c_22, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.58/1.87  tff(c_201, plain, (![A_99, A_100]: (r2_hidden(A_99, A_100) | ~r2_hidden(A_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_184, c_22])).
% 4.58/1.87  tff(c_399, plain, (![A_145, A_146]: (r2_hidden(A_145, A_146) | k1_tarski(A_145)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_356, c_201])).
% 4.58/1.87  tff(c_26, plain, (![A_15, B_16]: (~r2_hidden(A_15, k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.58/1.87  tff(c_449, plain, (![A_145]: (k1_tarski(A_145)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_399, c_26])).
% 4.58/1.87  tff(c_108, plain, (![A_79, B_80]: (r1_tarski(k1_tarski(A_79), B_80) | ~r2_hidden(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.58/1.87  tff(c_12, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.58/1.87  tff(c_113, plain, (![A_79]: (k1_tarski(A_79)=k1_xboole_0 | ~r2_hidden(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_108, c_12])).
% 4.58/1.87  tff(c_450, plain, (![A_79]: (~r2_hidden(A_79, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_449, c_113])).
% 4.58/1.87  tff(c_1441, plain, (![B_209]: (r2_hidden('#skF_8'(k1_xboole_0, B_209), B_209) | k2_relat_1(k1_xboole_0)=B_209)), inference(resolution, [status(thm)], [c_894, c_450])).
% 4.58/1.87  tff(c_1612, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1441, c_450])).
% 4.58/1.87  tff(c_36, plain, (![B_24, A_23]: (m1_subset_1(B_24, A_23) | ~v1_xboole_0(B_24) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.87  tff(c_34, plain, (![B_24, A_23]: (r2_hidden(B_24, A_23) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.87  tff(c_469, plain, (![A_153, C_154]: (r2_hidden(k4_tarski('#skF_9'(A_153, k2_relat_1(A_153), C_154), C_154), A_153) | ~r2_hidden(C_154, k2_relat_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.87  tff(c_502, plain, (![C_155]: (~r2_hidden(C_155, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_469, c_450])).
% 4.58/1.87  tff(c_512, plain, (![B_24]: (~m1_subset_1(B_24, k2_relat_1(k1_xboole_0)) | v1_xboole_0(k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_34, c_502])).
% 4.58/1.87  tff(c_536, plain, (![B_158]: (~m1_subset_1(B_158, k2_relat_1(k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_512])).
% 4.58/1.87  tff(c_541, plain, (![B_24]: (~v1_xboole_0(B_24) | ~v1_xboole_0(k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_36, c_536])).
% 4.58/1.87  tff(c_660, plain, (~v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_541])).
% 4.58/1.87  tff(c_1629, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_660])).
% 4.58/1.87  tff(c_1637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1629])).
% 4.58/1.87  tff(c_1638, plain, (![B_24]: (~v1_xboole_0(B_24))), inference(splitRight, [status(thm)], [c_541])).
% 4.58/1.87  tff(c_1651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1638, c_2])).
% 4.58/1.87  tff(c_1652, plain, (v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_512])).
% 4.58/1.87  tff(c_16, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.87  tff(c_1659, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1652, c_16])).
% 4.58/1.87  tff(c_1876, plain, (![A_233, B_234]: (r2_hidden(k4_tarski('#skF_7'(A_233, B_234), '#skF_6'(A_233, B_234)), A_233) | r2_hidden('#skF_8'(A_233, B_234), B_234) | k2_relat_1(A_233)=B_234)), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.87  tff(c_1916, plain, (![B_234]: (r2_hidden('#skF_8'(k1_xboole_0, B_234), B_234) | k2_relat_1(k1_xboole_0)=B_234)), inference(resolution, [status(thm)], [c_1876, c_450])).
% 4.58/1.87  tff(c_1955, plain, (![B_235]: (r2_hidden('#skF_8'(k1_xboole_0, B_235), B_235) | k1_xboole_0=B_235)), inference(demodulation, [status(thm), theory('equality')], [c_1659, c_1916])).
% 4.58/1.87  tff(c_1674, plain, (![C_213, A_214]: (r2_hidden(k4_tarski(C_213, '#skF_5'(A_214, k1_relat_1(A_214), C_213)), A_214) | ~r2_hidden(C_213, k1_relat_1(A_214)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.58/1.87  tff(c_1700, plain, (![C_213]: (~r2_hidden(C_213, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1674, c_450])).
% 4.58/1.87  tff(c_1991, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1955, c_1700])).
% 4.58/1.87  tff(c_2022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_1991])).
% 4.58/1.87  tff(c_2023, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 4.58/1.87  tff(c_2024, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 4.58/1.87  tff(c_2685, plain, (![A_335, B_336]: (r2_hidden(k4_tarski('#skF_2'(A_335, B_336), '#skF_3'(A_335, B_336)), A_335) | r2_hidden('#skF_4'(A_335, B_336), B_336) | k1_relat_1(A_335)=B_336)), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.58/1.87  tff(c_2253, plain, (![A_292, C_293, B_294]: (r2_hidden(A_292, C_293) | k3_xboole_0(k2_tarski(A_292, B_294), C_293)!=k2_tarski(A_292, B_294))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.58/1.87  tff(c_2266, plain, (![A_295, B_296]: (r2_hidden(A_295, k1_xboole_0) | k2_tarski(A_295, B_296)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_2253])).
% 4.58/1.87  tff(c_2269, plain, (![A_297]: (r2_hidden(A_297, k1_xboole_0) | k1_tarski(A_297)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_2266])).
% 4.58/1.87  tff(c_2083, plain, (![A_251, B_252, C_253]: (r1_tarski(A_251, B_252) | ~r1_tarski(A_251, k3_xboole_0(B_252, C_253)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.58/1.87  tff(c_2098, plain, (![A_254, A_255]: (r1_tarski(A_254, A_255) | ~r1_tarski(A_254, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2083])).
% 4.58/1.87  tff(c_2108, plain, (![A_256, A_257]: (r1_tarski(k1_tarski(A_256), A_257) | ~r2_hidden(A_256, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_2098])).
% 4.58/1.87  tff(c_2125, plain, (![A_256, A_257]: (r2_hidden(A_256, A_257) | ~r2_hidden(A_256, k1_xboole_0))), inference(resolution, [status(thm)], [c_2108, c_22])).
% 4.58/1.87  tff(c_2313, plain, (![A_300, A_301]: (r2_hidden(A_300, A_301) | k1_tarski(A_300)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2269, c_2125])).
% 4.58/1.87  tff(c_2353, plain, (![A_300]: (k1_tarski(A_300)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2313, c_26])).
% 4.58/1.87  tff(c_2033, plain, (![A_238, B_239]: (r1_tarski(k1_tarski(A_238), B_239) | ~r2_hidden(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.58/1.87  tff(c_2038, plain, (![A_238]: (k1_tarski(A_238)=k1_xboole_0 | ~r2_hidden(A_238, k1_xboole_0))), inference(resolution, [status(thm)], [c_2033, c_12])).
% 4.58/1.87  tff(c_2354, plain, (![A_238]: (~r2_hidden(A_238, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2353, c_2038])).
% 4.58/1.87  tff(c_2745, plain, (![B_336]: (r2_hidden('#skF_4'(k1_xboole_0, B_336), B_336) | k1_relat_1(k1_xboole_0)=B_336)), inference(resolution, [status(thm)], [c_2685, c_2354])).
% 4.58/1.87  tff(c_2779, plain, (![B_337]: (r2_hidden('#skF_4'(k1_xboole_0, B_337), B_337) | k1_xboole_0=B_337)), inference(demodulation, [status(thm), theory('equality')], [c_2024, c_2745])).
% 4.58/1.87  tff(c_58, plain, (![A_50, C_65]: (r2_hidden(k4_tarski('#skF_9'(A_50, k2_relat_1(A_50), C_65), C_65), A_50) | ~r2_hidden(C_65, k2_relat_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.87  tff(c_2387, plain, (![A_305]: (~r2_hidden(A_305, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2353, c_2038])).
% 4.58/1.87  tff(c_2396, plain, (![C_65]: (~r2_hidden(C_65, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_58, c_2387])).
% 4.58/1.87  tff(c_2835, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2779, c_2396])).
% 4.58/1.87  tff(c_2863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2023, c_2835])).
% 4.58/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.87  
% 4.58/1.87  Inference rules
% 4.58/1.87  ----------------------
% 4.58/1.87  #Ref     : 0
% 4.58/1.87  #Sup     : 550
% 4.58/1.87  #Fact    : 0
% 4.58/1.87  #Define  : 0
% 4.58/1.87  #Split   : 9
% 4.58/1.87  #Chain   : 0
% 4.58/1.87  #Close   : 0
% 4.58/1.87  
% 4.58/1.87  Ordering : KBO
% 4.58/1.87  
% 4.58/1.87  Simplification rules
% 4.58/1.87  ----------------------
% 4.58/1.87  #Subsume      : 72
% 4.58/1.87  #Demod        : 79
% 4.58/1.87  #Tautology    : 63
% 4.58/1.87  #SimpNegUnit  : 15
% 4.58/1.87  #BackRed      : 30
% 4.58/1.87  
% 4.58/1.87  #Partial instantiations: 0
% 4.58/1.87  #Strategies tried      : 1
% 4.58/1.87  
% 4.58/1.87  Timing (in seconds)
% 4.58/1.87  ----------------------
% 4.58/1.87  Preprocessing        : 0.34
% 4.58/1.87  Parsing              : 0.17
% 4.58/1.87  CNF conversion       : 0.03
% 4.58/1.87  Main loop            : 0.75
% 4.58/1.87  Inferencing          : 0.26
% 4.58/1.87  Reduction            : 0.21
% 4.58/1.87  Demodulation         : 0.12
% 4.58/1.87  BG Simplification    : 0.04
% 4.58/1.87  Subsumption          : 0.17
% 4.58/1.87  Abstraction          : 0.04
% 4.58/1.87  MUC search           : 0.00
% 4.58/1.87  Cooper               : 0.00
% 4.58/1.87  Total                : 1.12
% 4.58/1.87  Index Insertion      : 0.00
% 4.58/1.87  Index Deletion       : 0.00
% 4.58/1.87  Index Matching       : 0.00
% 4.58/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
