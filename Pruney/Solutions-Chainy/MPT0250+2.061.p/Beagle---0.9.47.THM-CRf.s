%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:40 EST 2020

% Result     : Theorem 13.55s
% Output     : CNFRefutation 13.55s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 554 expanded)
%              Number of leaves         :   36 ( 200 expanded)
%              Depth                    :   22
%              Number of atoms          :  101 ( 627 expanded)
%              Number of equality atoms :   49 ( 379 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_367,plain,(
    ! [D_129,C_130,B_131,A_132] : k2_enumset1(D_129,C_130,B_131,A_132) = k2_enumset1(A_132,B_131,C_130,D_129) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_51,B_52,C_53] : k2_enumset1(A_51,A_51,B_52,C_53) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_383,plain,(
    ! [D_129,C_130,B_131] : k2_enumset1(D_129,C_130,B_131,B_131) = k1_enumset1(B_131,C_130,D_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_24])).

tff(c_26,plain,(
    ! [A_54,B_55,C_56,D_57] : k3_enumset1(A_54,A_54,B_55,C_56,D_57) = k2_enumset1(A_54,B_55,C_56,D_57) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [B_59,A_58,E_62,D_61,C_60] : k4_enumset1(A_58,A_58,B_59,C_60,D_61,E_62) = k3_enumset1(A_58,B_59,C_60,D_61,E_62) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [D_66,F_68,B_64,C_65,A_63,E_67] : k5_enumset1(A_63,A_63,B_64,C_65,D_66,E_67,F_68) = k4_enumset1(A_63,B_64,C_65,D_66,E_67,F_68) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [B_70,F_74,G_75,E_73,D_72,C_71,A_69] : k6_enumset1(A_69,A_69,B_70,C_71,D_72,E_73,F_74,G_75) = k5_enumset1(A_69,B_70,C_71,D_72,E_73,F_74,G_75) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_783,plain,(
    ! [B_200,C_206,D_204,A_203,G_199,H_201,E_202,F_205] : k2_xboole_0(k2_enumset1(A_203,B_200,C_206,D_204),k2_enumset1(E_202,F_205,G_199,H_201)) = k6_enumset1(A_203,B_200,C_206,D_204,E_202,F_205,G_199,H_201) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_832,plain,(
    ! [B_52,G_199,H_201,E_202,F_205,C_53,A_51] : k6_enumset1(A_51,A_51,B_52,C_53,E_202,F_205,G_199,H_201) = k2_xboole_0(k1_enumset1(A_51,B_52,C_53),k2_enumset1(E_202,F_205,G_199,H_201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_783])).

tff(c_2032,plain,(
    ! [F_401,H_400,E_397,C_398,A_395,G_399,B_396] : k2_xboole_0(k1_enumset1(A_395,B_396,C_398),k2_enumset1(E_397,F_401,G_399,H_400)) = k5_enumset1(A_395,B_396,C_398,E_397,F_401,G_399,H_400) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_832])).

tff(c_2223,plain,(
    ! [A_424,G_427,H_428,E_426,C_429,F_425,B_430] : r1_tarski(k1_enumset1(A_424,B_430,C_429),k5_enumset1(A_424,B_430,C_429,E_426,F_425,G_427,H_428)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2032,c_8])).

tff(c_2229,plain,(
    ! [D_66,F_68,B_64,C_65,A_63,E_67] : r1_tarski(k1_enumset1(A_63,A_63,B_64),k4_enumset1(A_63,B_64,C_65,D_66,E_67,F_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2223])).

tff(c_2242,plain,(
    ! [C_432,D_436,E_431,F_435,B_433,A_434] : r1_tarski(k2_tarski(A_434,B_433),k4_enumset1(A_434,B_433,C_432,D_436,E_431,F_435)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2229])).

tff(c_38,plain,(
    ! [B_79,C_80,A_78] :
      ( r2_hidden(B_79,C_80)
      | ~ r1_tarski(k2_tarski(A_78,B_79),C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2290,plain,(
    ! [D_439,B_440,F_438,C_441,E_437,A_442] : r2_hidden(B_440,k4_enumset1(A_442,B_440,C_441,D_439,E_437,F_438)) ),
    inference(resolution,[status(thm)],[c_2242,c_38])).

tff(c_2300,plain,(
    ! [E_446,D_444,C_447,A_445,B_443] : r2_hidden(A_445,k3_enumset1(A_445,B_443,C_447,D_444,E_446)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2290])).

tff(c_2310,plain,(
    ! [A_448,B_449,C_450,D_451] : r2_hidden(A_448,k2_enumset1(A_448,B_449,C_450,D_451)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2300])).

tff(c_2317,plain,(
    ! [D_129,B_131,C_130] : r2_hidden(D_129,k1_enumset1(B_131,C_130,D_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_2310])).

tff(c_2326,plain,(
    ! [A_51,B_52,C_53] : r2_hidden(A_51,k1_enumset1(A_51,B_52,C_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2310])).

tff(c_879,plain,(
    ! [E_216,G_215,B_222,A_217,F_219,C_220,H_221,D_218] : k2_xboole_0(k5_enumset1(A_217,B_222,C_220,D_218,E_216,F_219,G_215),k1_tarski(H_221)) = k6_enumset1(A_217,B_222,C_220,D_218,E_216,F_219,G_215,H_221) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_906,plain,(
    ! [D_66,F_68,B_64,C_65,A_63,H_221,E_67] : k6_enumset1(A_63,A_63,B_64,C_65,D_66,E_67,F_68,H_221) = k2_xboole_0(k4_enumset1(A_63,B_64,C_65,D_66,E_67,F_68),k1_tarski(H_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_879])).

tff(c_2156,plain,(
    ! [E_413,F_418,C_414,D_419,B_416,A_417,H_415] : k2_xboole_0(k4_enumset1(A_417,B_416,C_414,D_419,E_413,F_418),k1_tarski(H_415)) = k5_enumset1(A_417,B_416,C_414,D_419,E_413,F_418,H_415) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_906])).

tff(c_2189,plain,(
    ! [B_59,A_58,E_62,D_61,C_60,H_415] : k5_enumset1(A_58,A_58,B_59,C_60,D_61,E_62,H_415) = k2_xboole_0(k3_enumset1(A_58,B_59,C_60,D_61,E_62),k1_tarski(H_415)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2156])).

tff(c_14427,plain,(
    ! [E_1914,C_1915,B_1910,H_1912,D_1911,A_1913] : k2_xboole_0(k3_enumset1(A_1913,B_1910,C_1915,D_1911,E_1914),k1_tarski(H_1912)) = k4_enumset1(A_1913,B_1910,C_1915,D_1911,E_1914,H_1912) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2189])).

tff(c_14910,plain,(
    ! [C_1979,E_1976,A_1980,D_1977,H_1978,B_1981] : r1_tarski(k3_enumset1(A_1980,B_1981,C_1979,D_1977,E_1976),k4_enumset1(A_1980,B_1981,C_1979,D_1977,E_1976,H_1978)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14427,c_8])).

tff(c_14916,plain,(
    ! [B_59,A_58,E_62,D_61,C_60] : r1_tarski(k3_enumset1(A_58,A_58,B_59,C_60,D_61),k3_enumset1(A_58,B_59,C_60,D_61,E_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14910])).

tff(c_14923,plain,(
    ! [A_1984,C_1986,E_1985,B_1982,D_1983] : r1_tarski(k2_enumset1(A_1984,B_1982,C_1986,D_1983),k3_enumset1(A_1984,B_1982,C_1986,D_1983,E_1985)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14916])).

tff(c_14929,plain,(
    ! [A_54,B_55,C_56,D_57] : r1_tarski(k2_enumset1(A_54,A_54,B_55,C_56),k2_enumset1(A_54,B_55,C_56,D_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_14923])).

tff(c_14945,plain,(
    ! [A_1987,B_1988,C_1989,D_1990] : r1_tarski(k1_enumset1(A_1987,B_1988,C_1989),k2_enumset1(A_1987,B_1988,C_1989,D_1990)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14929])).

tff(c_15131,plain,(
    ! [D_1996,C_1997,B_1998] : r1_tarski(k1_enumset1(D_1996,C_1997,B_1998),k1_enumset1(B_1998,C_1997,D_1996)) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_14945])).

tff(c_15179,plain,(
    ! [B_2001,A_2002] : r1_tarski(k1_enumset1(B_2001,A_2002,A_2002),k2_tarski(A_2002,B_2001)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_15131])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16342,plain,(
    ! [B_2105,A_2106] : k3_xboole_0(k1_enumset1(B_2105,A_2106,A_2106),k2_tarski(A_2106,B_2105)) = k1_enumset1(B_2105,A_2106,A_2106) ),
    inference(resolution,[status(thm)],[c_15179,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_661,plain,(
    ! [A_154,B_155,C_156] :
      ( r1_tarski(k2_tarski(A_154,B_155),C_156)
      | ~ r2_hidden(B_155,C_156)
      | ~ r2_hidden(A_154,C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1196,plain,(
    ! [A_261,B_262,C_263] :
      ( k3_xboole_0(k2_tarski(A_261,B_262),C_263) = k2_tarski(A_261,B_262)
      | ~ r2_hidden(B_262,C_263)
      | ~ r2_hidden(A_261,C_263) ) ),
    inference(resolution,[status(thm)],[c_661,c_6])).

tff(c_1252,plain,(
    ! [B_2,A_261,B_262] :
      ( k3_xboole_0(B_2,k2_tarski(A_261,B_262)) = k2_tarski(A_261,B_262)
      | ~ r2_hidden(B_262,B_2)
      | ~ r2_hidden(A_261,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1196])).

tff(c_16348,plain,(
    ! [B_2105,A_2106] :
      ( k1_enumset1(B_2105,A_2106,A_2106) = k2_tarski(A_2106,B_2105)
      | ~ r2_hidden(B_2105,k1_enumset1(B_2105,A_2106,A_2106))
      | ~ r2_hidden(A_2106,k1_enumset1(B_2105,A_2106,A_2106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16342,c_1252])).

tff(c_16383,plain,(
    ! [B_2105,A_2106] : k1_enumset1(B_2105,A_2106,A_2106) = k2_tarski(A_2106,B_2105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2317,c_2326,c_16348])).

tff(c_414,plain,(
    ! [D_133,C_134,B_135] : k2_enumset1(D_133,C_134,B_135,B_135) = k1_enumset1(B_135,C_134,D_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_24])).

tff(c_427,plain,(
    ! [C_134,B_135] : k1_enumset1(C_134,B_135,B_135) = k1_enumset1(B_135,C_134,C_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_24])).

tff(c_16625,plain,(
    ! [C_2109,B_2110] : k2_tarski(C_2109,B_2110) = k2_tarski(B_2110,C_2109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16383,c_16383,c_427])).

tff(c_34,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_17549,plain,(
    ! [B_2122,C_2123] : k3_tarski(k2_tarski(B_2122,C_2123)) = k2_xboole_0(C_2123,B_2122) ),
    inference(superposition,[status(thm),theory(equality)],[c_16625,c_34])).

tff(c_17555,plain,(
    ! [C_2123,B_2122] : k2_xboole_0(C_2123,B_2122) = k2_xboole_0(B_2122,C_2123) ),
    inference(superposition,[status(thm),theory(equality)],[c_17549,c_34])).

tff(c_44,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_95,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_137,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_17575,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) = k2_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17555,c_17555,c_137])).

tff(c_17578,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17575])).

tff(c_20,plain,(
    ! [A_48] : k2_tarski(A_48,A_48) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_262,plain,(
    ! [A_116,C_117,B_118] :
      ( r1_tarski(A_116,k2_xboole_0(C_117,B_118))
      | ~ r1_tarski(A_116,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_282,plain,(
    ! [B_79,C_117,B_118,A_78] :
      ( r2_hidden(B_79,k2_xboole_0(C_117,B_118))
      | ~ r1_tarski(k2_tarski(A_78,B_79),B_118) ) ),
    inference(resolution,[status(thm)],[c_262,c_38])).

tff(c_3079,plain,(
    ! [E_564,C_569,B_568,D_567,C_565,A_570,F_566] : r2_hidden(B_568,k2_xboole_0(C_565,k4_enumset1(A_570,B_568,C_569,D_567,E_564,F_566))) ),
    inference(resolution,[status(thm)],[c_2242,c_282])).

tff(c_3093,plain,(
    ! [D_572,C_576,A_573,C_575,B_571,E_574] : r2_hidden(A_573,k2_xboole_0(C_575,k3_enumset1(A_573,B_571,C_576,D_572,E_574))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3079])).

tff(c_3107,plain,(
    ! [C_577,D_581,A_579,B_580,C_578] : r2_hidden(A_579,k2_xboole_0(C_577,k2_enumset1(A_579,B_580,C_578,D_581))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3093])).

tff(c_3139,plain,(
    ! [A_582,C_583,B_584,C_585] : r2_hidden(A_582,k2_xboole_0(C_583,k1_enumset1(A_582,B_584,C_585))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3107])).

tff(c_3165,plain,(
    ! [A_586,C_587,B_588] : r2_hidden(A_586,k2_xboole_0(C_587,k2_tarski(A_586,B_588))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3139])).

tff(c_3176,plain,(
    ! [A_48,C_587] : r2_hidden(A_48,k2_xboole_0(C_587,k1_tarski(A_48))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3165])).

tff(c_19035,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17578,c_3176])).

tff(c_19068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_19035])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.55/6.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.55/6.19  
% 13.55/6.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.55/6.20  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 13.55/6.20  
% 13.55/6.20  %Foreground sorts:
% 13.55/6.20  
% 13.55/6.20  
% 13.55/6.20  %Background operators:
% 13.55/6.20  
% 13.55/6.20  
% 13.55/6.20  %Foreground operators:
% 13.55/6.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.55/6.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.55/6.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.55/6.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.55/6.20  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.55/6.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.55/6.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.55/6.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.55/6.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.55/6.20  tff('#skF_2', type, '#skF_2': $i).
% 13.55/6.20  tff('#skF_1', type, '#skF_1': $i).
% 13.55/6.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.55/6.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.55/6.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.55/6.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.55/6.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.55/6.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.55/6.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.55/6.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.55/6.20  
% 13.55/6.22  tff(f_74, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 13.55/6.22  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.55/6.22  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.55/6.22  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 13.55/6.22  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 13.55/6.22  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 13.55/6.22  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 13.55/6.22  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.55/6.22  tff(f_59, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 13.55/6.22  tff(f_61, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 13.55/6.22  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 13.55/6.22  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 13.55/6.22  tff(f_47, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 13.55/6.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.55/6.22  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.55/6.22  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.55/6.22  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 13.55/6.22  tff(c_42, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.55/6.22  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.55/6.22  tff(c_88, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.55/6.22  tff(c_96, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(resolution, [status(thm)], [c_8, c_88])).
% 13.55/6.22  tff(c_367, plain, (![D_129, C_130, B_131, A_132]: (k2_enumset1(D_129, C_130, B_131, A_132)=k2_enumset1(A_132, B_131, C_130, D_129))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.55/6.22  tff(c_24, plain, (![A_51, B_52, C_53]: (k2_enumset1(A_51, A_51, B_52, C_53)=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.55/6.22  tff(c_383, plain, (![D_129, C_130, B_131]: (k2_enumset1(D_129, C_130, B_131, B_131)=k1_enumset1(B_131, C_130, D_129))), inference(superposition, [status(thm), theory('equality')], [c_367, c_24])).
% 13.55/6.22  tff(c_26, plain, (![A_54, B_55, C_56, D_57]: (k3_enumset1(A_54, A_54, B_55, C_56, D_57)=k2_enumset1(A_54, B_55, C_56, D_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.55/6.22  tff(c_28, plain, (![B_59, A_58, E_62, D_61, C_60]: (k4_enumset1(A_58, A_58, B_59, C_60, D_61, E_62)=k3_enumset1(A_58, B_59, C_60, D_61, E_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.55/6.22  tff(c_22, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.55/6.22  tff(c_30, plain, (![D_66, F_68, B_64, C_65, A_63, E_67]: (k5_enumset1(A_63, A_63, B_64, C_65, D_66, E_67, F_68)=k4_enumset1(A_63, B_64, C_65, D_66, E_67, F_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.55/6.22  tff(c_32, plain, (![B_70, F_74, G_75, E_73, D_72, C_71, A_69]: (k6_enumset1(A_69, A_69, B_70, C_71, D_72, E_73, F_74, G_75)=k5_enumset1(A_69, B_70, C_71, D_72, E_73, F_74, G_75))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.55/6.22  tff(c_783, plain, (![B_200, C_206, D_204, A_203, G_199, H_201, E_202, F_205]: (k2_xboole_0(k2_enumset1(A_203, B_200, C_206, D_204), k2_enumset1(E_202, F_205, G_199, H_201))=k6_enumset1(A_203, B_200, C_206, D_204, E_202, F_205, G_199, H_201))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.55/6.22  tff(c_832, plain, (![B_52, G_199, H_201, E_202, F_205, C_53, A_51]: (k6_enumset1(A_51, A_51, B_52, C_53, E_202, F_205, G_199, H_201)=k2_xboole_0(k1_enumset1(A_51, B_52, C_53), k2_enumset1(E_202, F_205, G_199, H_201)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_783])).
% 13.55/6.22  tff(c_2032, plain, (![F_401, H_400, E_397, C_398, A_395, G_399, B_396]: (k2_xboole_0(k1_enumset1(A_395, B_396, C_398), k2_enumset1(E_397, F_401, G_399, H_400))=k5_enumset1(A_395, B_396, C_398, E_397, F_401, G_399, H_400))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_832])).
% 13.55/6.22  tff(c_2223, plain, (![A_424, G_427, H_428, E_426, C_429, F_425, B_430]: (r1_tarski(k1_enumset1(A_424, B_430, C_429), k5_enumset1(A_424, B_430, C_429, E_426, F_425, G_427, H_428)))), inference(superposition, [status(thm), theory('equality')], [c_2032, c_8])).
% 13.55/6.22  tff(c_2229, plain, (![D_66, F_68, B_64, C_65, A_63, E_67]: (r1_tarski(k1_enumset1(A_63, A_63, B_64), k4_enumset1(A_63, B_64, C_65, D_66, E_67, F_68)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2223])).
% 13.55/6.22  tff(c_2242, plain, (![C_432, D_436, E_431, F_435, B_433, A_434]: (r1_tarski(k2_tarski(A_434, B_433), k4_enumset1(A_434, B_433, C_432, D_436, E_431, F_435)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2229])).
% 13.55/6.22  tff(c_38, plain, (![B_79, C_80, A_78]: (r2_hidden(B_79, C_80) | ~r1_tarski(k2_tarski(A_78, B_79), C_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.55/6.22  tff(c_2290, plain, (![D_439, B_440, F_438, C_441, E_437, A_442]: (r2_hidden(B_440, k4_enumset1(A_442, B_440, C_441, D_439, E_437, F_438)))), inference(resolution, [status(thm)], [c_2242, c_38])).
% 13.55/6.22  tff(c_2300, plain, (![E_446, D_444, C_447, A_445, B_443]: (r2_hidden(A_445, k3_enumset1(A_445, B_443, C_447, D_444, E_446)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2290])).
% 13.55/6.22  tff(c_2310, plain, (![A_448, B_449, C_450, D_451]: (r2_hidden(A_448, k2_enumset1(A_448, B_449, C_450, D_451)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2300])).
% 13.55/6.22  tff(c_2317, plain, (![D_129, B_131, C_130]: (r2_hidden(D_129, k1_enumset1(B_131, C_130, D_129)))), inference(superposition, [status(thm), theory('equality')], [c_383, c_2310])).
% 13.55/6.22  tff(c_2326, plain, (![A_51, B_52, C_53]: (r2_hidden(A_51, k1_enumset1(A_51, B_52, C_53)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2310])).
% 13.55/6.22  tff(c_879, plain, (![E_216, G_215, B_222, A_217, F_219, C_220, H_221, D_218]: (k2_xboole_0(k5_enumset1(A_217, B_222, C_220, D_218, E_216, F_219, G_215), k1_tarski(H_221))=k6_enumset1(A_217, B_222, C_220, D_218, E_216, F_219, G_215, H_221))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.55/6.22  tff(c_906, plain, (![D_66, F_68, B_64, C_65, A_63, H_221, E_67]: (k6_enumset1(A_63, A_63, B_64, C_65, D_66, E_67, F_68, H_221)=k2_xboole_0(k4_enumset1(A_63, B_64, C_65, D_66, E_67, F_68), k1_tarski(H_221)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_879])).
% 13.55/6.22  tff(c_2156, plain, (![E_413, F_418, C_414, D_419, B_416, A_417, H_415]: (k2_xboole_0(k4_enumset1(A_417, B_416, C_414, D_419, E_413, F_418), k1_tarski(H_415))=k5_enumset1(A_417, B_416, C_414, D_419, E_413, F_418, H_415))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_906])).
% 13.55/6.22  tff(c_2189, plain, (![B_59, A_58, E_62, D_61, C_60, H_415]: (k5_enumset1(A_58, A_58, B_59, C_60, D_61, E_62, H_415)=k2_xboole_0(k3_enumset1(A_58, B_59, C_60, D_61, E_62), k1_tarski(H_415)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2156])).
% 13.55/6.22  tff(c_14427, plain, (![E_1914, C_1915, B_1910, H_1912, D_1911, A_1913]: (k2_xboole_0(k3_enumset1(A_1913, B_1910, C_1915, D_1911, E_1914), k1_tarski(H_1912))=k4_enumset1(A_1913, B_1910, C_1915, D_1911, E_1914, H_1912))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2189])).
% 13.55/6.22  tff(c_14910, plain, (![C_1979, E_1976, A_1980, D_1977, H_1978, B_1981]: (r1_tarski(k3_enumset1(A_1980, B_1981, C_1979, D_1977, E_1976), k4_enumset1(A_1980, B_1981, C_1979, D_1977, E_1976, H_1978)))), inference(superposition, [status(thm), theory('equality')], [c_14427, c_8])).
% 13.55/6.22  tff(c_14916, plain, (![B_59, A_58, E_62, D_61, C_60]: (r1_tarski(k3_enumset1(A_58, A_58, B_59, C_60, D_61), k3_enumset1(A_58, B_59, C_60, D_61, E_62)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_14910])).
% 13.55/6.22  tff(c_14923, plain, (![A_1984, C_1986, E_1985, B_1982, D_1983]: (r1_tarski(k2_enumset1(A_1984, B_1982, C_1986, D_1983), k3_enumset1(A_1984, B_1982, C_1986, D_1983, E_1985)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14916])).
% 13.55/6.22  tff(c_14929, plain, (![A_54, B_55, C_56, D_57]: (r1_tarski(k2_enumset1(A_54, A_54, B_55, C_56), k2_enumset1(A_54, B_55, C_56, D_57)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_14923])).
% 13.55/6.22  tff(c_14945, plain, (![A_1987, B_1988, C_1989, D_1990]: (r1_tarski(k1_enumset1(A_1987, B_1988, C_1989), k2_enumset1(A_1987, B_1988, C_1989, D_1990)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14929])).
% 13.55/6.22  tff(c_15131, plain, (![D_1996, C_1997, B_1998]: (r1_tarski(k1_enumset1(D_1996, C_1997, B_1998), k1_enumset1(B_1998, C_1997, D_1996)))), inference(superposition, [status(thm), theory('equality')], [c_383, c_14945])).
% 13.55/6.22  tff(c_15179, plain, (![B_2001, A_2002]: (r1_tarski(k1_enumset1(B_2001, A_2002, A_2002), k2_tarski(A_2002, B_2001)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_15131])).
% 13.55/6.22  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.55/6.22  tff(c_16342, plain, (![B_2105, A_2106]: (k3_xboole_0(k1_enumset1(B_2105, A_2106, A_2106), k2_tarski(A_2106, B_2105))=k1_enumset1(B_2105, A_2106, A_2106))), inference(resolution, [status(thm)], [c_15179, c_6])).
% 13.55/6.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.55/6.22  tff(c_661, plain, (![A_154, B_155, C_156]: (r1_tarski(k2_tarski(A_154, B_155), C_156) | ~r2_hidden(B_155, C_156) | ~r2_hidden(A_154, C_156))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.55/6.22  tff(c_1196, plain, (![A_261, B_262, C_263]: (k3_xboole_0(k2_tarski(A_261, B_262), C_263)=k2_tarski(A_261, B_262) | ~r2_hidden(B_262, C_263) | ~r2_hidden(A_261, C_263))), inference(resolution, [status(thm)], [c_661, c_6])).
% 13.55/6.22  tff(c_1252, plain, (![B_2, A_261, B_262]: (k3_xboole_0(B_2, k2_tarski(A_261, B_262))=k2_tarski(A_261, B_262) | ~r2_hidden(B_262, B_2) | ~r2_hidden(A_261, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1196])).
% 13.55/6.22  tff(c_16348, plain, (![B_2105, A_2106]: (k1_enumset1(B_2105, A_2106, A_2106)=k2_tarski(A_2106, B_2105) | ~r2_hidden(B_2105, k1_enumset1(B_2105, A_2106, A_2106)) | ~r2_hidden(A_2106, k1_enumset1(B_2105, A_2106, A_2106)))), inference(superposition, [status(thm), theory('equality')], [c_16342, c_1252])).
% 13.55/6.22  tff(c_16383, plain, (![B_2105, A_2106]: (k1_enumset1(B_2105, A_2106, A_2106)=k2_tarski(A_2106, B_2105))), inference(demodulation, [status(thm), theory('equality')], [c_2317, c_2326, c_16348])).
% 13.55/6.22  tff(c_414, plain, (![D_133, C_134, B_135]: (k2_enumset1(D_133, C_134, B_135, B_135)=k1_enumset1(B_135, C_134, D_133))), inference(superposition, [status(thm), theory('equality')], [c_367, c_24])).
% 13.55/6.22  tff(c_427, plain, (![C_134, B_135]: (k1_enumset1(C_134, B_135, B_135)=k1_enumset1(B_135, C_134, C_134))), inference(superposition, [status(thm), theory('equality')], [c_414, c_24])).
% 13.55/6.22  tff(c_16625, plain, (![C_2109, B_2110]: (k2_tarski(C_2109, B_2110)=k2_tarski(B_2110, C_2109))), inference(demodulation, [status(thm), theory('equality')], [c_16383, c_16383, c_427])).
% 13.55/6.22  tff(c_34, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.55/6.22  tff(c_17549, plain, (![B_2122, C_2123]: (k3_tarski(k2_tarski(B_2122, C_2123))=k2_xboole_0(C_2123, B_2122))), inference(superposition, [status(thm), theory('equality')], [c_16625, c_34])).
% 13.55/6.22  tff(c_17555, plain, (![C_2123, B_2122]: (k2_xboole_0(C_2123, B_2122)=k2_xboole_0(B_2122, C_2123))), inference(superposition, [status(thm), theory('equality')], [c_17549, c_34])).
% 13.55/6.22  tff(c_44, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.55/6.22  tff(c_95, plain, (k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_44, c_88])).
% 13.55/6.22  tff(c_137, plain, (k3_xboole_0('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2, c_95])).
% 13.55/6.22  tff(c_17575, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))=k2_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17555, c_17555, c_137])).
% 13.55/6.22  tff(c_17578, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17575])).
% 13.55/6.22  tff(c_20, plain, (![A_48]: (k2_tarski(A_48, A_48)=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.55/6.22  tff(c_262, plain, (![A_116, C_117, B_118]: (r1_tarski(A_116, k2_xboole_0(C_117, B_118)) | ~r1_tarski(A_116, B_118))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.55/6.22  tff(c_282, plain, (![B_79, C_117, B_118, A_78]: (r2_hidden(B_79, k2_xboole_0(C_117, B_118)) | ~r1_tarski(k2_tarski(A_78, B_79), B_118))), inference(resolution, [status(thm)], [c_262, c_38])).
% 13.55/6.22  tff(c_3079, plain, (![E_564, C_569, B_568, D_567, C_565, A_570, F_566]: (r2_hidden(B_568, k2_xboole_0(C_565, k4_enumset1(A_570, B_568, C_569, D_567, E_564, F_566))))), inference(resolution, [status(thm)], [c_2242, c_282])).
% 13.55/6.22  tff(c_3093, plain, (![D_572, C_576, A_573, C_575, B_571, E_574]: (r2_hidden(A_573, k2_xboole_0(C_575, k3_enumset1(A_573, B_571, C_576, D_572, E_574))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3079])).
% 13.55/6.22  tff(c_3107, plain, (![C_577, D_581, A_579, B_580, C_578]: (r2_hidden(A_579, k2_xboole_0(C_577, k2_enumset1(A_579, B_580, C_578, D_581))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3093])).
% 13.55/6.22  tff(c_3139, plain, (![A_582, C_583, B_584, C_585]: (r2_hidden(A_582, k2_xboole_0(C_583, k1_enumset1(A_582, B_584, C_585))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3107])).
% 13.55/6.22  tff(c_3165, plain, (![A_586, C_587, B_588]: (r2_hidden(A_586, k2_xboole_0(C_587, k2_tarski(A_586, B_588))))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3139])).
% 13.55/6.22  tff(c_3176, plain, (![A_48, C_587]: (r2_hidden(A_48, k2_xboole_0(C_587, k1_tarski(A_48))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3165])).
% 13.55/6.22  tff(c_19035, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17578, c_3176])).
% 13.55/6.22  tff(c_19068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_19035])).
% 13.55/6.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.55/6.22  
% 13.55/6.22  Inference rules
% 13.55/6.22  ----------------------
% 13.55/6.22  #Ref     : 0
% 13.55/6.22  #Sup     : 5174
% 13.55/6.22  #Fact    : 0
% 13.55/6.22  #Define  : 0
% 13.55/6.22  #Split   : 1
% 13.55/6.22  #Chain   : 0
% 13.55/6.22  #Close   : 0
% 13.55/6.22  
% 13.55/6.22  Ordering : KBO
% 13.55/6.22  
% 13.55/6.22  Simplification rules
% 13.55/6.22  ----------------------
% 13.55/6.22  #Subsume      : 402
% 13.55/6.22  #Demod        : 1496
% 13.55/6.22  #Tautology    : 1505
% 13.55/6.22  #SimpNegUnit  : 1
% 13.55/6.22  #BackRed      : 22
% 13.55/6.22  
% 13.55/6.22  #Partial instantiations: 0
% 13.55/6.22  #Strategies tried      : 1
% 13.55/6.22  
% 13.55/6.22  Timing (in seconds)
% 13.55/6.22  ----------------------
% 13.55/6.22  Preprocessing        : 0.36
% 13.55/6.22  Parsing              : 0.20
% 13.55/6.22  CNF conversion       : 0.02
% 13.55/6.22  Main loop            : 5.02
% 13.55/6.22  Inferencing          : 0.93
% 13.55/6.22  Reduction            : 2.58
% 13.55/6.22  Demodulation         : 2.26
% 13.55/6.22  BG Simplification    : 0.10
% 13.55/6.22  Subsumption          : 1.13
% 13.55/6.22  Abstraction          : 0.11
% 13.55/6.22  MUC search           : 0.00
% 13.55/6.22  Cooper               : 0.00
% 13.55/6.22  Total                : 5.43
% 13.55/6.22  Index Insertion      : 0.00
% 13.55/6.22  Index Deletion       : 0.00
% 13.55/6.22  Index Matching       : 0.00
% 13.55/6.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
