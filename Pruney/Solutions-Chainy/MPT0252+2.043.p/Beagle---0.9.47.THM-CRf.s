%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:06 EST 2020

% Result     : Theorem 17.66s
% Output     : CNFRefutation 17.66s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 321 expanded)
%              Number of leaves         :   33 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :   85 ( 354 expanded)
%              Number of equality atoms :   40 ( 224 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_281,plain,(
    ! [B_120,D_121,C_122,A_123] : k2_enumset1(B_120,D_121,C_122,A_123) = k2_enumset1(A_123,B_120,C_122,D_121) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1944,plain,(
    ! [C_202,A_203,B_204] : k2_enumset1(C_202,A_203,B_204,A_203) = k1_enumset1(A_203,B_204,C_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_281])).

tff(c_324,plain,(
    ! [C_124,D_125,A_126,B_127] : k2_enumset1(C_124,D_125,A_126,B_127) = k2_enumset1(A_126,B_127,C_124,D_125) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_386,plain,(
    ! [B_45,C_46,A_44] : k2_enumset1(B_45,C_46,A_44,A_44) = k1_enumset1(A_44,B_45,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_324])).

tff(c_1951,plain,(
    ! [A_203,C_202] : k1_enumset1(A_203,C_202,A_203) = k1_enumset1(A_203,A_203,C_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_1944,c_386])).

tff(c_2004,plain,(
    ! [A_203,C_202] : k1_enumset1(A_203,C_202,A_203) = k2_tarski(A_203,C_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1951])).

tff(c_26,plain,(
    ! [C_25,D_26,A_23,B_24] : k2_enumset1(C_25,D_26,A_23,B_24) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_444,plain,(
    ! [B_131,C_132,A_133] : k2_enumset1(B_131,C_132,A_133,A_133) = k1_enumset1(A_133,B_131,C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_324])).

tff(c_24,plain,(
    ! [B_20,D_22,C_21,A_19] : k2_enumset1(B_20,D_22,C_21,A_19) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2125,plain,(
    ! [A_210,B_211,C_212] : k2_enumset1(A_210,B_211,A_210,C_212) = k1_enumset1(A_210,B_211,C_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_24])).

tff(c_2183,plain,(
    ! [C_25,D_26,B_24] : k2_enumset1(C_25,D_26,C_25,B_24) = k1_enumset1(C_25,B_24,D_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2125])).

tff(c_38,plain,(
    ! [A_47,B_48,C_49,D_50] : k3_enumset1(A_47,A_47,B_48,C_49,D_50) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] : k4_enumset1(A_51,A_51,B_52,C_53,D_54,E_55) = k3_enumset1(A_51,B_52,C_53,D_54,E_55) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1529,plain,(
    ! [B_180,A_181,C_177,D_178,F_176,E_179] : k2_xboole_0(k3_enumset1(A_181,B_180,C_177,D_178,E_179),k1_tarski(F_176)) = k4_enumset1(A_181,B_180,C_177,D_178,E_179,F_176) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1547,plain,(
    ! [A_47,D_50,F_176,C_49,B_48] : k4_enumset1(A_47,A_47,B_48,C_49,D_50,F_176) = k2_xboole_0(k2_enumset1(A_47,B_48,C_49,D_50),k1_tarski(F_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1529])).

tff(c_8831,plain,(
    ! [C_290,B_289,D_287,A_286,F_288] : k2_xboole_0(k2_enumset1(A_286,B_289,C_290,D_287),k1_tarski(F_288)) = k3_enumset1(A_286,B_289,C_290,D_287,F_288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1547])).

tff(c_28386,plain,(
    ! [D_420,C_418,A_421,B_422,F_419] : r1_tarski(k2_enumset1(A_421,B_422,C_418,D_420),k3_enumset1(A_421,B_422,C_418,D_420,F_419)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8831,c_16])).

tff(c_28469,plain,(
    ! [A_44,B_45,C_46,F_419] : r1_tarski(k1_enumset1(A_44,B_45,C_46),k3_enumset1(A_44,A_44,B_45,C_46,F_419)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_28386])).

tff(c_40301,plain,(
    ! [A_460,B_461,C_462,F_463] : r1_tarski(k1_enumset1(A_460,B_461,C_462),k2_enumset1(A_460,B_461,C_462,F_463)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28469])).

tff(c_40330,plain,(
    ! [C_25,D_26,B_24] : r1_tarski(k1_enumset1(C_25,D_26,C_25),k1_enumset1(C_25,B_24,D_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2183,c_40301])).

tff(c_40410,plain,(
    ! [C_464,D_465,B_466] : r1_tarski(k2_tarski(C_464,D_465),k1_enumset1(C_464,B_466,D_465)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_40330])).

tff(c_50,plain,(
    ! [B_72,C_73,A_71] :
      ( r2_hidden(B_72,C_73)
      | ~ r1_tarski(k2_tarski(A_71,B_72),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40442,plain,(
    ! [D_465,C_464,B_466] : r2_hidden(D_465,k1_enumset1(C_464,B_466,D_465)) ),
    inference(resolution,[status(thm)],[c_40410,c_50])).

tff(c_52,plain,(
    ! [A_71,C_73,B_72] :
      ( r2_hidden(A_71,C_73)
      | ~ r1_tarski(k2_tarski(A_71,B_72),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40440,plain,(
    ! [C_464,B_466,D_465] : r2_hidden(C_464,k1_enumset1(C_464,B_466,D_465)) ),
    inference(resolution,[status(thm)],[c_40410,c_52])).

tff(c_486,plain,(
    ! [B_20,D_22,A_19] : k2_enumset1(B_20,D_22,D_22,A_19) = k1_enumset1(D_22,A_19,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_444])).

tff(c_41939,plain,(
    ! [B_487,D_488,A_489] : r1_tarski(k1_enumset1(B_487,D_488,D_488),k1_enumset1(D_488,A_489,B_487)) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_40301])).

tff(c_41980,plain,(
    ! [B_490,A_491] : r1_tarski(k1_enumset1(B_490,A_491,A_491),k2_tarski(A_491,B_490)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_41939])).

tff(c_1007,plain,(
    ! [A_153,B_154,C_155] :
      ( r1_tarski(k2_tarski(A_153,B_154),C_155)
      | ~ r2_hidden(B_154,C_155)
      | ~ r2_hidden(A_153,C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1025,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_tarski(A_153,B_154) = C_155
      | ~ r1_tarski(C_155,k2_tarski(A_153,B_154))
      | ~ r2_hidden(B_154,C_155)
      | ~ r2_hidden(A_153,C_155) ) ),
    inference(resolution,[status(thm)],[c_1007,c_8])).

tff(c_41983,plain,(
    ! [B_490,A_491] :
      ( k1_enumset1(B_490,A_491,A_491) = k2_tarski(A_491,B_490)
      | ~ r2_hidden(B_490,k1_enumset1(B_490,A_491,A_491))
      | ~ r2_hidden(A_491,k1_enumset1(B_490,A_491,A_491)) ) ),
    inference(resolution,[status(thm)],[c_41980,c_1025])).

tff(c_42005,plain,(
    ! [B_490,A_491] : k1_enumset1(B_490,A_491,A_491) = k2_tarski(A_491,B_490) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40442,c_40440,c_41983])).

tff(c_467,plain,(
    ! [C_132,A_133] : k1_enumset1(C_132,A_133,A_133) = k1_enumset1(A_133,C_132,C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_36])).

tff(c_42081,plain,(
    ! [C_494,A_495] : k2_tarski(C_494,A_495) = k2_tarski(A_495,C_494) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42005,c_42005,c_467])).

tff(c_46,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42366,plain,(
    ! [A_504,C_505] : k3_tarski(k2_tarski(A_504,C_505)) = k2_xboole_0(C_505,A_504) ),
    inference(superposition,[status(thm),theory(equality)],[c_42081,c_46])).

tff(c_42372,plain,(
    ! [C_505,A_504] : k2_xboole_0(C_505,A_504) = k2_xboole_0(A_504,C_505) ),
    inference(superposition,[status(thm),theory(equality)],[c_42366,c_46])).

tff(c_56,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_185,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(B_95,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_185])).

tff(c_220,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_42396,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42372,c_220])).

tff(c_42401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42396])).

tff(c_42402,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_42409,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42402,c_16])).

tff(c_42435,plain,(
    ! [A_509,C_510,B_511] :
      ( r2_hidden(A_509,C_510)
      | ~ r1_tarski(k2_tarski(A_509,B_511),C_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42438,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42409,c_42435])).

tff(c_42453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_42438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:53:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.66/10.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.66/10.57  
% 17.66/10.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.66/10.57  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 17.66/10.57  
% 17.66/10.57  %Foreground sorts:
% 17.66/10.57  
% 17.66/10.57  
% 17.66/10.57  %Background operators:
% 17.66/10.57  
% 17.66/10.57  
% 17.66/10.57  %Foreground operators:
% 17.66/10.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.66/10.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.66/10.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.66/10.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.66/10.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.66/10.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.66/10.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.66/10.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.66/10.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.66/10.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.66/10.57  tff('#skF_2', type, '#skF_2': $i).
% 17.66/10.57  tff('#skF_3', type, '#skF_3': $i).
% 17.66/10.57  tff('#skF_1', type, '#skF_1': $i).
% 17.66/10.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.66/10.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.66/10.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.66/10.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.66/10.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.66/10.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.66/10.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.66/10.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.66/10.57  
% 17.66/10.58  tff(f_82, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 17.66/10.58  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 17.66/10.58  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 17.66/10.58  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 17.66/10.58  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 17.66/10.58  tff(f_51, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 17.66/10.58  tff(f_63, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 17.66/10.58  tff(f_65, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 17.66/10.58  tff(f_53, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 17.66/10.58  tff(f_77, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 17.66/10.58  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.66/10.58  tff(f_71, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 17.66/10.58  tff(c_54, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.66/10.58  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.66/10.58  tff(c_34, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.66/10.58  tff(c_36, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.66/10.58  tff(c_281, plain, (![B_120, D_121, C_122, A_123]: (k2_enumset1(B_120, D_121, C_122, A_123)=k2_enumset1(A_123, B_120, C_122, D_121))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.66/10.58  tff(c_1944, plain, (![C_202, A_203, B_204]: (k2_enumset1(C_202, A_203, B_204, A_203)=k1_enumset1(A_203, B_204, C_202))), inference(superposition, [status(thm), theory('equality')], [c_36, c_281])).
% 17.66/10.58  tff(c_324, plain, (![C_124, D_125, A_126, B_127]: (k2_enumset1(C_124, D_125, A_126, B_127)=k2_enumset1(A_126, B_127, C_124, D_125))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.66/10.58  tff(c_386, plain, (![B_45, C_46, A_44]: (k2_enumset1(B_45, C_46, A_44, A_44)=k1_enumset1(A_44, B_45, C_46))), inference(superposition, [status(thm), theory('equality')], [c_36, c_324])).
% 17.66/10.58  tff(c_1951, plain, (![A_203, C_202]: (k1_enumset1(A_203, C_202, A_203)=k1_enumset1(A_203, A_203, C_202))), inference(superposition, [status(thm), theory('equality')], [c_1944, c_386])).
% 17.66/10.58  tff(c_2004, plain, (![A_203, C_202]: (k1_enumset1(A_203, C_202, A_203)=k2_tarski(A_203, C_202))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1951])).
% 17.66/10.58  tff(c_26, plain, (![C_25, D_26, A_23, B_24]: (k2_enumset1(C_25, D_26, A_23, B_24)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.66/10.58  tff(c_444, plain, (![B_131, C_132, A_133]: (k2_enumset1(B_131, C_132, A_133, A_133)=k1_enumset1(A_133, B_131, C_132))), inference(superposition, [status(thm), theory('equality')], [c_36, c_324])).
% 17.66/10.58  tff(c_24, plain, (![B_20, D_22, C_21, A_19]: (k2_enumset1(B_20, D_22, C_21, A_19)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.66/10.58  tff(c_2125, plain, (![A_210, B_211, C_212]: (k2_enumset1(A_210, B_211, A_210, C_212)=k1_enumset1(A_210, B_211, C_212))), inference(superposition, [status(thm), theory('equality')], [c_444, c_24])).
% 17.66/10.58  tff(c_2183, plain, (![C_25, D_26, B_24]: (k2_enumset1(C_25, D_26, C_25, B_24)=k1_enumset1(C_25, B_24, D_26))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2125])).
% 17.66/10.58  tff(c_38, plain, (![A_47, B_48, C_49, D_50]: (k3_enumset1(A_47, A_47, B_48, C_49, D_50)=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.66/10.58  tff(c_40, plain, (![B_52, E_55, C_53, D_54, A_51]: (k4_enumset1(A_51, A_51, B_52, C_53, D_54, E_55)=k3_enumset1(A_51, B_52, C_53, D_54, E_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.66/10.58  tff(c_1529, plain, (![B_180, A_181, C_177, D_178, F_176, E_179]: (k2_xboole_0(k3_enumset1(A_181, B_180, C_177, D_178, E_179), k1_tarski(F_176))=k4_enumset1(A_181, B_180, C_177, D_178, E_179, F_176))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.66/10.58  tff(c_1547, plain, (![A_47, D_50, F_176, C_49, B_48]: (k4_enumset1(A_47, A_47, B_48, C_49, D_50, F_176)=k2_xboole_0(k2_enumset1(A_47, B_48, C_49, D_50), k1_tarski(F_176)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1529])).
% 17.66/10.58  tff(c_8831, plain, (![C_290, B_289, D_287, A_286, F_288]: (k2_xboole_0(k2_enumset1(A_286, B_289, C_290, D_287), k1_tarski(F_288))=k3_enumset1(A_286, B_289, C_290, D_287, F_288))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1547])).
% 17.66/10.58  tff(c_28386, plain, (![D_420, C_418, A_421, B_422, F_419]: (r1_tarski(k2_enumset1(A_421, B_422, C_418, D_420), k3_enumset1(A_421, B_422, C_418, D_420, F_419)))), inference(superposition, [status(thm), theory('equality')], [c_8831, c_16])).
% 17.66/10.58  tff(c_28469, plain, (![A_44, B_45, C_46, F_419]: (r1_tarski(k1_enumset1(A_44, B_45, C_46), k3_enumset1(A_44, A_44, B_45, C_46, F_419)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_28386])).
% 17.66/10.58  tff(c_40301, plain, (![A_460, B_461, C_462, F_463]: (r1_tarski(k1_enumset1(A_460, B_461, C_462), k2_enumset1(A_460, B_461, C_462, F_463)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28469])).
% 17.66/10.58  tff(c_40330, plain, (![C_25, D_26, B_24]: (r1_tarski(k1_enumset1(C_25, D_26, C_25), k1_enumset1(C_25, B_24, D_26)))), inference(superposition, [status(thm), theory('equality')], [c_2183, c_40301])).
% 17.66/10.58  tff(c_40410, plain, (![C_464, D_465, B_466]: (r1_tarski(k2_tarski(C_464, D_465), k1_enumset1(C_464, B_466, D_465)))), inference(demodulation, [status(thm), theory('equality')], [c_2004, c_40330])).
% 17.66/10.58  tff(c_50, plain, (![B_72, C_73, A_71]: (r2_hidden(B_72, C_73) | ~r1_tarski(k2_tarski(A_71, B_72), C_73))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.66/10.58  tff(c_40442, plain, (![D_465, C_464, B_466]: (r2_hidden(D_465, k1_enumset1(C_464, B_466, D_465)))), inference(resolution, [status(thm)], [c_40410, c_50])).
% 17.66/10.58  tff(c_52, plain, (![A_71, C_73, B_72]: (r2_hidden(A_71, C_73) | ~r1_tarski(k2_tarski(A_71, B_72), C_73))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.66/10.58  tff(c_40440, plain, (![C_464, B_466, D_465]: (r2_hidden(C_464, k1_enumset1(C_464, B_466, D_465)))), inference(resolution, [status(thm)], [c_40410, c_52])).
% 17.66/10.58  tff(c_486, plain, (![B_20, D_22, A_19]: (k2_enumset1(B_20, D_22, D_22, A_19)=k1_enumset1(D_22, A_19, B_20))), inference(superposition, [status(thm), theory('equality')], [c_24, c_444])).
% 17.66/10.58  tff(c_41939, plain, (![B_487, D_488, A_489]: (r1_tarski(k1_enumset1(B_487, D_488, D_488), k1_enumset1(D_488, A_489, B_487)))), inference(superposition, [status(thm), theory('equality')], [c_486, c_40301])).
% 17.66/10.58  tff(c_41980, plain, (![B_490, A_491]: (r1_tarski(k1_enumset1(B_490, A_491, A_491), k2_tarski(A_491, B_490)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_41939])).
% 17.66/10.58  tff(c_1007, plain, (![A_153, B_154, C_155]: (r1_tarski(k2_tarski(A_153, B_154), C_155) | ~r2_hidden(B_154, C_155) | ~r2_hidden(A_153, C_155))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.66/10.58  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.66/10.58  tff(c_1025, plain, (![A_153, B_154, C_155]: (k2_tarski(A_153, B_154)=C_155 | ~r1_tarski(C_155, k2_tarski(A_153, B_154)) | ~r2_hidden(B_154, C_155) | ~r2_hidden(A_153, C_155))), inference(resolution, [status(thm)], [c_1007, c_8])).
% 17.66/10.58  tff(c_41983, plain, (![B_490, A_491]: (k1_enumset1(B_490, A_491, A_491)=k2_tarski(A_491, B_490) | ~r2_hidden(B_490, k1_enumset1(B_490, A_491, A_491)) | ~r2_hidden(A_491, k1_enumset1(B_490, A_491, A_491)))), inference(resolution, [status(thm)], [c_41980, c_1025])).
% 17.66/10.58  tff(c_42005, plain, (![B_490, A_491]: (k1_enumset1(B_490, A_491, A_491)=k2_tarski(A_491, B_490))), inference(demodulation, [status(thm), theory('equality')], [c_40442, c_40440, c_41983])).
% 17.66/10.58  tff(c_467, plain, (![C_132, A_133]: (k1_enumset1(C_132, A_133, A_133)=k1_enumset1(A_133, C_132, C_132))), inference(superposition, [status(thm), theory('equality')], [c_444, c_36])).
% 17.66/10.58  tff(c_42081, plain, (![C_494, A_495]: (k2_tarski(C_494, A_495)=k2_tarski(A_495, C_494))), inference(demodulation, [status(thm), theory('equality')], [c_42005, c_42005, c_467])).
% 17.66/10.58  tff(c_46, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.66/10.58  tff(c_42366, plain, (![A_504, C_505]: (k3_tarski(k2_tarski(A_504, C_505))=k2_xboole_0(C_505, A_504))), inference(superposition, [status(thm), theory('equality')], [c_42081, c_46])).
% 17.66/10.58  tff(c_42372, plain, (![C_505, A_504]: (k2_xboole_0(C_505, A_504)=k2_xboole_0(A_504, C_505))), inference(superposition, [status(thm), theory('equality')], [c_42366, c_46])).
% 17.66/10.58  tff(c_56, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.66/10.58  tff(c_185, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(B_95, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.66/10.58  tff(c_194, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_185])).
% 17.66/10.58  tff(c_220, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_194])).
% 17.66/10.58  tff(c_42396, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42372, c_220])).
% 17.66/10.58  tff(c_42401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_42396])).
% 17.66/10.58  tff(c_42402, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_194])).
% 17.66/10.58  tff(c_42409, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42402, c_16])).
% 17.66/10.58  tff(c_42435, plain, (![A_509, C_510, B_511]: (r2_hidden(A_509, C_510) | ~r1_tarski(k2_tarski(A_509, B_511), C_510))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.66/10.58  tff(c_42438, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42409, c_42435])).
% 17.66/10.58  tff(c_42453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_42438])).
% 17.66/10.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.66/10.58  
% 17.66/10.58  Inference rules
% 17.66/10.58  ----------------------
% 17.66/10.58  #Ref     : 0
% 17.66/10.58  #Sup     : 11221
% 17.66/10.58  #Fact    : 0
% 17.66/10.58  #Define  : 0
% 17.66/10.58  #Split   : 1
% 17.66/10.58  #Chain   : 0
% 17.66/10.58  #Close   : 0
% 17.66/10.58  
% 17.66/10.58  Ordering : KBO
% 17.66/10.58  
% 17.66/10.58  Simplification rules
% 17.66/10.58  ----------------------
% 17.66/10.58  #Subsume      : 873
% 17.66/10.58  #Demod        : 14702
% 17.66/10.58  #Tautology    : 3813
% 17.66/10.58  #SimpNegUnit  : 1
% 17.66/10.58  #BackRed      : 10
% 17.66/10.58  
% 17.66/10.58  #Partial instantiations: 0
% 17.66/10.58  #Strategies tried      : 1
% 17.66/10.58  
% 17.66/10.58  Timing (in seconds)
% 17.66/10.58  ----------------------
% 17.66/10.59  Preprocessing        : 0.36
% 17.66/10.59  Parsing              : 0.19
% 17.66/10.59  CNF conversion       : 0.02
% 17.66/10.59  Main loop            : 9.39
% 17.66/10.59  Inferencing          : 1.10
% 17.66/10.59  Reduction            : 6.80
% 17.66/10.59  Demodulation         : 6.48
% 17.66/10.59  BG Simplification    : 0.20
% 17.66/10.59  Subsumption          : 1.05
% 17.66/10.59  Abstraction          : 0.32
% 17.66/10.59  MUC search           : 0.00
% 17.66/10.59  Cooper               : 0.00
% 17.66/10.59  Total                : 9.78
% 17.66/10.59  Index Insertion      : 0.00
% 17.66/10.59  Index Deletion       : 0.00
% 17.66/10.59  Index Matching       : 0.00
% 17.66/10.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
