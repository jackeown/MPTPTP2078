%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:21 EST 2020

% Result     : Theorem 16.95s
% Output     : CNFRefutation 17.07s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 269 expanded)
%              Number of leaves         :   40 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 ( 430 expanded)
%              Number of equality atoms :   74 ( 177 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_93,axiom,(
    ! [A,B,C,D] : k4_xboole_0(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A,C),B),k2_zfmisc_1(A,k4_xboole_0(B,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_223,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(A_79,B_80)
      | k4_xboole_0(A_79,B_80) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_130,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_231,plain,(
    k4_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_223,c_130])).

tff(c_141,plain,(
    ! [A_72,B_73] : k2_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = A_72 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_147,plain,(
    ! [A_72] : k3_xboole_0(A_72,A_72) = A_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_18])).

tff(c_826,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_1'(A_128,B_129),k3_xboole_0(A_128,B_129))
      | r1_xboole_0(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_880,plain,(
    ! [A_132] :
      ( r2_hidden('#skF_1'(A_132,A_132),A_132)
      | r1_xboole_0(A_132,A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_826])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_275,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,k3_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_298,plain,(
    ! [A_95,C_96] :
      ( ~ r1_xboole_0(A_95,A_95)
      | ~ r2_hidden(C_96,A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_275])).

tff(c_301,plain,(
    ! [C_96,B_2] :
      ( ~ r2_hidden(C_96,B_2)
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_298])).

tff(c_303,plain,(
    ! [C_96,B_2] :
      ( ~ r2_hidden(C_96,B_2)
      | k1_xboole_0 != B_2 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_301])).

tff(c_892,plain,(
    ! [A_132] :
      ( k1_xboole_0 != A_132
      | r1_xboole_0(A_132,A_132) ) ),
    inference(resolution,[status(thm)],[c_880,c_303])).

tff(c_60,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_236,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = A_81
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_244,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_236])).

tff(c_8,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_307,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(C_7,k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_8])).

tff(c_511,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_841,plain,
    ( r2_hidden('#skF_1'(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')),k2_zfmisc_1('#skF_3','#skF_4'))
    | r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_826])).

tff(c_854,plain,(
    r2_hidden('#skF_1'(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_511,c_841])).

tff(c_930,plain,(
    ! [C_137,D_138,A_139,B_140] :
      ( ~ r1_xboole_0(C_137,D_138)
      | r1_xboole_0(k2_zfmisc_1(A_139,C_137),k2_zfmisc_1(B_140,D_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_278,plain,(
    ! [A_72,C_93] :
      ( ~ r1_xboole_0(A_72,A_72)
      | ~ r2_hidden(C_93,A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_275])).

tff(c_969,plain,(
    ! [C_141,B_142,D_143] :
      ( ~ r2_hidden(C_141,k2_zfmisc_1(B_142,D_143))
      | ~ r1_xboole_0(D_143,D_143) ) ),
    inference(resolution,[status(thm)],[c_930,c_278])).

tff(c_982,plain,(
    ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_854,c_969])).

tff(c_993,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_892,c_982])).

tff(c_24,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_217,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k1_xboole_0
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_221,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_217])).

tff(c_2243,plain,(
    ! [A_219,C_220,B_221,D_222] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_219,C_220),B_221),k2_zfmisc_1(A_219,k4_xboole_0(B_221,D_222))) = k4_xboole_0(k2_zfmisc_1(A_219,B_221),k2_zfmisc_1(C_220,D_222)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5139,plain,(
    ! [A_304,C_305,B_306,D_307] : k3_xboole_0(k2_zfmisc_1(k4_xboole_0(A_304,C_305),B_306),k4_xboole_0(k2_zfmisc_1(A_304,B_306),k2_zfmisc_1(C_305,D_307))) = k2_zfmisc_1(k4_xboole_0(A_304,C_305),B_306) ),
    inference(superposition,[status(thm),theory(equality)],[c_2243,c_18])).

tff(c_5378,plain,(
    k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_5'),'#skF_4'),k1_xboole_0) = k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_5139])).

tff(c_5428,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5378])).

tff(c_44,plain,(
    ! [B_54,A_53] :
      ( k1_xboole_0 = B_54
      | k1_xboole_0 = A_53
      | k2_zfmisc_1(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5496,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5428,c_44])).

tff(c_5528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_993,c_5496])).

tff(c_5533,plain,(
    ! [C_308] : ~ r2_hidden(C_308,k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_5537,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_5533])).

tff(c_5541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5537])).

tff(c_5543,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5678,plain,(
    ! [A_327,B_328] :
      ( k3_xboole_0(A_327,B_328) = A_327
      | ~ r1_tarski(A_327,B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5690,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5543,c_5678])).

tff(c_5985,plain,(
    ! [A_343,B_344,C_345] :
      ( ~ r1_xboole_0(A_343,B_344)
      | ~ r2_hidden(C_345,k3_xboole_0(A_343,B_344)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5994,plain,(
    ! [C_345] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_345,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5690,c_5985])).

tff(c_6037,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5994])).

tff(c_6040,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_6037])).

tff(c_6042,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5690,c_6040])).

tff(c_5647,plain,(
    ! [A_321,B_322] :
      ( r1_tarski(A_321,B_322)
      | k4_xboole_0(A_321,B_322) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5542,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5651,plain,(
    k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5647,c_5542])).

tff(c_5554,plain,(
    ! [A_312,B_313] : k2_xboole_0(A_312,k3_xboole_0(A_312,B_313)) = A_312 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5569,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5554])).

tff(c_5560,plain,(
    ! [A_312] : k3_xboole_0(A_312,A_312) = A_312 ),
    inference(superposition,[status(thm),theory(equality)],[c_5554,c_18])).

tff(c_6298,plain,(
    ! [A_371,B_372] :
      ( r2_hidden('#skF_1'(A_371,B_372),k3_xboole_0(A_371,B_372))
      | r1_xboole_0(A_371,B_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6364,plain,(
    ! [A_375] :
      ( r2_hidden('#skF_1'(A_375,A_375),A_375)
      | r1_xboole_0(A_375,A_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5560,c_6298])).

tff(c_6043,plain,(
    ! [A_348,C_349] :
      ( ~ r1_xboole_0(A_348,A_348)
      | ~ r2_hidden(C_349,A_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5560,c_5985])).

tff(c_6046,plain,(
    ! [C_349,B_2] :
      ( ~ r2_hidden(C_349,B_2)
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_6043])).

tff(c_6048,plain,(
    ! [C_349,B_2] :
      ( ~ r2_hidden(C_349,B_2)
      | k1_xboole_0 != B_2 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5560,c_6046])).

tff(c_6376,plain,(
    ! [A_375] :
      ( k1_xboole_0 != A_375
      | r1_xboole_0(A_375,A_375) ) ),
    inference(resolution,[status(thm)],[c_6364,c_6048])).

tff(c_6390,plain,(
    ! [A_377,B_378,C_379,D_380] :
      ( ~ r1_xboole_0(A_377,B_378)
      | r1_xboole_0(k2_zfmisc_1(A_377,C_379),k2_zfmisc_1(B_378,D_380)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5997,plain,(
    ! [A_312,C_345] :
      ( ~ r1_xboole_0(A_312,A_312)
      | ~ r2_hidden(C_345,A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5560,c_5985])).

tff(c_6421,plain,(
    ! [C_381,B_382,D_383] :
      ( ~ r2_hidden(C_381,k2_zfmisc_1(B_382,D_383))
      | ~ r1_xboole_0(B_382,B_382) ) ),
    inference(resolution,[status(thm)],[c_6390,c_5997])).

tff(c_6436,plain,(
    ! [B_384,D_385] :
      ( ~ r1_xboole_0(B_384,B_384)
      | k2_zfmisc_1(B_384,D_385) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_6421])).

tff(c_6475,plain,(
    ! [D_385] : k2_zfmisc_1(k1_xboole_0,D_385) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6376,c_6436])).

tff(c_5652,plain,(
    ! [A_323,B_324] :
      ( k4_xboole_0(A_323,B_324) = k1_xboole_0
      | ~ r1_tarski(A_323,B_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5664,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5543,c_5652])).

tff(c_7483,plain,(
    ! [A_453,C_454,B_455,D_456] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_453,C_454),B_455),k2_zfmisc_1(A_453,k4_xboole_0(B_455,D_456))) = k4_xboole_0(k2_zfmisc_1(A_453,B_455),k2_zfmisc_1(C_454,D_456)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5632,plain,(
    ! [A_319,B_320] : k3_tarski(k2_tarski(A_319,B_320)) = k2_xboole_0(A_319,B_320) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5708,plain,(
    ! [B_331,A_332] : k3_tarski(k2_tarski(B_331,A_332)) = k2_xboole_0(A_332,B_331) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5632])).

tff(c_42,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5714,plain,(
    ! [B_331,A_332] : k2_xboole_0(B_331,A_332) = k2_xboole_0(A_332,B_331) ),
    inference(superposition,[status(thm),theory(equality)],[c_5708,c_42])).

tff(c_34566,plain,(
    ! [A_893,B_894,D_895,C_896] : k2_xboole_0(k2_zfmisc_1(A_893,k4_xboole_0(B_894,D_895)),k2_zfmisc_1(k4_xboole_0(A_893,C_896),B_894)) = k4_xboole_0(k2_zfmisc_1(A_893,B_894),k2_zfmisc_1(C_896,D_895)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7483,c_5714])).

tff(c_35037,plain,(
    ! [B_894,D_895] : k2_xboole_0(k2_zfmisc_1('#skF_3',k4_xboole_0(B_894,D_895)),k2_zfmisc_1(k1_xboole_0,B_894)) = k4_xboole_0(k2_zfmisc_1('#skF_3',B_894),k2_zfmisc_1('#skF_5',D_895)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5664,c_34566])).

tff(c_61239,plain,(
    ! [B_1195,D_1196] : k4_xboole_0(k2_zfmisc_1('#skF_3',B_1195),k2_zfmisc_1('#skF_5',D_1196)) = k2_zfmisc_1('#skF_3',k4_xboole_0(B_1195,D_1196)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5569,c_6475,c_35037])).

tff(c_5663,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_5652])).

tff(c_61420,plain,(
    k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61239,c_5663])).

tff(c_61935,plain,
    ( k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_61420,c_44])).

tff(c_62055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6042,c_5651,c_61935])).

tff(c_62058,plain,(
    ! [C_1197] : ~ r2_hidden(C_1197,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5994])).

tff(c_62063,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_62058])).

tff(c_48,plain,(
    ! [B_54] : k2_zfmisc_1(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62092,plain,(
    ! [B_54] : k2_zfmisc_1('#skF_3',B_54) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62063,c_62063,c_48])).

tff(c_62096,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62063,c_58])).

tff(c_62211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62092,c_62096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.95/9.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.95/9.31  
% 16.95/9.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.95/9.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 16.95/9.32  
% 16.95/9.32  %Foreground sorts:
% 16.95/9.32  
% 16.95/9.32  
% 16.95/9.32  %Background operators:
% 16.95/9.32  
% 16.95/9.32  
% 16.95/9.32  %Foreground operators:
% 16.95/9.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 16.95/9.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.95/9.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.95/9.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.95/9.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.95/9.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.95/9.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.95/9.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.95/9.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.95/9.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.95/9.32  tff('#skF_5', type, '#skF_5': $i).
% 16.95/9.32  tff('#skF_6', type, '#skF_6': $i).
% 16.95/9.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.95/9.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.95/9.32  tff('#skF_3', type, '#skF_3': $i).
% 16.95/9.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.95/9.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.95/9.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.95/9.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.95/9.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.95/9.32  tff('#skF_4', type, '#skF_4': $i).
% 16.95/9.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.95/9.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.95/9.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.95/9.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.95/9.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.95/9.32  
% 17.07/9.34  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 17.07/9.34  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 17.07/9.34  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 17.07/9.34  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 17.07/9.34  tff(f_59, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 17.07/9.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 17.07/9.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 17.07/9.34  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.07/9.34  tff(f_99, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 17.07/9.34  tff(f_67, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 17.07/9.34  tff(f_93, axiom, (![A, B, C, D]: (k4_xboole_0(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A, C), B), k2_zfmisc_1(A, k4_xboole_0(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_zfmisc_1)).
% 17.07/9.34  tff(f_91, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 17.07/9.34  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 17.07/9.34  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 17.07/9.34  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.07/9.34  tff(c_58, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.07/9.34  tff(c_223, plain, (![A_79, B_80]: (r1_tarski(A_79, B_80) | k4_xboole_0(A_79, B_80)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.07/9.34  tff(c_56, plain, (~r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.07/9.34  tff(c_130, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 17.07/9.34  tff(c_231, plain, (k4_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_223, c_130])).
% 17.07/9.34  tff(c_141, plain, (![A_72, B_73]: (k2_xboole_0(A_72, k3_xboole_0(A_72, B_73))=A_72)), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.07/9.34  tff(c_18, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.07/9.34  tff(c_147, plain, (![A_72]: (k3_xboole_0(A_72, A_72)=A_72)), inference(superposition, [status(thm), theory('equality')], [c_141, c_18])).
% 17.07/9.34  tff(c_826, plain, (![A_128, B_129]: (r2_hidden('#skF_1'(A_128, B_129), k3_xboole_0(A_128, B_129)) | r1_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.07/9.34  tff(c_880, plain, (![A_132]: (r2_hidden('#skF_1'(A_132, A_132), A_132) | r1_xboole_0(A_132, A_132))), inference(superposition, [status(thm), theory('equality')], [c_147, c_826])).
% 17.07/9.34  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 17.07/9.34  tff(c_275, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, k3_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.07/9.34  tff(c_298, plain, (![A_95, C_96]: (~r1_xboole_0(A_95, A_95) | ~r2_hidden(C_96, A_95))), inference(superposition, [status(thm), theory('equality')], [c_147, c_275])).
% 17.07/9.34  tff(c_301, plain, (![C_96, B_2]: (~r2_hidden(C_96, B_2) | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_298])).
% 17.07/9.34  tff(c_303, plain, (![C_96, B_2]: (~r2_hidden(C_96, B_2) | k1_xboole_0!=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_301])).
% 17.07/9.34  tff(c_892, plain, (![A_132]: (k1_xboole_0!=A_132 | r1_xboole_0(A_132, A_132))), inference(resolution, [status(thm)], [c_880, c_303])).
% 17.07/9.34  tff(c_60, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.07/9.34  tff(c_236, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=A_81 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.07/9.34  tff(c_244, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_236])).
% 17.07/9.34  tff(c_8, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.07/9.34  tff(c_307, plain, (![C_7]: (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(C_7, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_244, c_8])).
% 17.07/9.34  tff(c_511, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_307])).
% 17.07/9.34  tff(c_841, plain, (r2_hidden('#skF_1'(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')), k2_zfmisc_1('#skF_3', '#skF_4')) | r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_826])).
% 17.07/9.34  tff(c_854, plain, (r2_hidden('#skF_1'(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_511, c_841])).
% 17.07/9.34  tff(c_930, plain, (![C_137, D_138, A_139, B_140]: (~r1_xboole_0(C_137, D_138) | r1_xboole_0(k2_zfmisc_1(A_139, C_137), k2_zfmisc_1(B_140, D_138)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.07/9.34  tff(c_278, plain, (![A_72, C_93]: (~r1_xboole_0(A_72, A_72) | ~r2_hidden(C_93, A_72))), inference(superposition, [status(thm), theory('equality')], [c_147, c_275])).
% 17.07/9.34  tff(c_969, plain, (![C_141, B_142, D_143]: (~r2_hidden(C_141, k2_zfmisc_1(B_142, D_143)) | ~r1_xboole_0(D_143, D_143))), inference(resolution, [status(thm)], [c_930, c_278])).
% 17.07/9.34  tff(c_982, plain, (~r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_854, c_969])).
% 17.07/9.34  tff(c_993, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_892, c_982])).
% 17.07/9.34  tff(c_24, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 17.07/9.34  tff(c_217, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k1_xboole_0 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.07/9.34  tff(c_221, plain, (k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_217])).
% 17.07/9.34  tff(c_2243, plain, (![A_219, C_220, B_221, D_222]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_219, C_220), B_221), k2_zfmisc_1(A_219, k4_xboole_0(B_221, D_222)))=k4_xboole_0(k2_zfmisc_1(A_219, B_221), k2_zfmisc_1(C_220, D_222)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.07/9.34  tff(c_5139, plain, (![A_304, C_305, B_306, D_307]: (k3_xboole_0(k2_zfmisc_1(k4_xboole_0(A_304, C_305), B_306), k4_xboole_0(k2_zfmisc_1(A_304, B_306), k2_zfmisc_1(C_305, D_307)))=k2_zfmisc_1(k4_xboole_0(A_304, C_305), B_306))), inference(superposition, [status(thm), theory('equality')], [c_2243, c_18])).
% 17.07/9.34  tff(c_5378, plain, (k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4'), k1_xboole_0)=k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_221, c_5139])).
% 17.07/9.34  tff(c_5428, plain, (k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5378])).
% 17.07/9.34  tff(c_44, plain, (![B_54, A_53]: (k1_xboole_0=B_54 | k1_xboole_0=A_53 | k2_zfmisc_1(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 17.07/9.34  tff(c_5496, plain, (k1_xboole_0='#skF_4' | k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5428, c_44])).
% 17.07/9.34  tff(c_5528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_993, c_5496])).
% 17.07/9.34  tff(c_5533, plain, (![C_308]: (~r2_hidden(C_308, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_307])).
% 17.07/9.34  tff(c_5537, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_5533])).
% 17.07/9.34  tff(c_5541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_5537])).
% 17.07/9.34  tff(c_5543, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 17.07/9.34  tff(c_5678, plain, (![A_327, B_328]: (k3_xboole_0(A_327, B_328)=A_327 | ~r1_tarski(A_327, B_328))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.07/9.34  tff(c_5690, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_5543, c_5678])).
% 17.07/9.34  tff(c_5985, plain, (![A_343, B_344, C_345]: (~r1_xboole_0(A_343, B_344) | ~r2_hidden(C_345, k3_xboole_0(A_343, B_344)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.07/9.34  tff(c_5994, plain, (![C_345]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_345, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5690, c_5985])).
% 17.07/9.34  tff(c_6037, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_5994])).
% 17.07/9.34  tff(c_6040, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_6037])).
% 17.07/9.34  tff(c_6042, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5690, c_6040])).
% 17.07/9.34  tff(c_5647, plain, (![A_321, B_322]: (r1_tarski(A_321, B_322) | k4_xboole_0(A_321, B_322)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.07/9.34  tff(c_5542, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 17.07/9.34  tff(c_5651, plain, (k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_5647, c_5542])).
% 17.07/9.34  tff(c_5554, plain, (![A_312, B_313]: (k2_xboole_0(A_312, k3_xboole_0(A_312, B_313))=A_312)), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.07/9.34  tff(c_5569, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(superposition, [status(thm), theory('equality')], [c_24, c_5554])).
% 17.07/9.34  tff(c_5560, plain, (![A_312]: (k3_xboole_0(A_312, A_312)=A_312)), inference(superposition, [status(thm), theory('equality')], [c_5554, c_18])).
% 17.07/9.34  tff(c_6298, plain, (![A_371, B_372]: (r2_hidden('#skF_1'(A_371, B_372), k3_xboole_0(A_371, B_372)) | r1_xboole_0(A_371, B_372))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.07/9.34  tff(c_6364, plain, (![A_375]: (r2_hidden('#skF_1'(A_375, A_375), A_375) | r1_xboole_0(A_375, A_375))), inference(superposition, [status(thm), theory('equality')], [c_5560, c_6298])).
% 17.07/9.34  tff(c_6043, plain, (![A_348, C_349]: (~r1_xboole_0(A_348, A_348) | ~r2_hidden(C_349, A_348))), inference(superposition, [status(thm), theory('equality')], [c_5560, c_5985])).
% 17.07/9.34  tff(c_6046, plain, (![C_349, B_2]: (~r2_hidden(C_349, B_2) | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_6043])).
% 17.07/9.34  tff(c_6048, plain, (![C_349, B_2]: (~r2_hidden(C_349, B_2) | k1_xboole_0!=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_5560, c_6046])).
% 17.07/9.34  tff(c_6376, plain, (![A_375]: (k1_xboole_0!=A_375 | r1_xboole_0(A_375, A_375))), inference(resolution, [status(thm)], [c_6364, c_6048])).
% 17.07/9.34  tff(c_6390, plain, (![A_377, B_378, C_379, D_380]: (~r1_xboole_0(A_377, B_378) | r1_xboole_0(k2_zfmisc_1(A_377, C_379), k2_zfmisc_1(B_378, D_380)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.07/9.34  tff(c_5997, plain, (![A_312, C_345]: (~r1_xboole_0(A_312, A_312) | ~r2_hidden(C_345, A_312))), inference(superposition, [status(thm), theory('equality')], [c_5560, c_5985])).
% 17.07/9.34  tff(c_6421, plain, (![C_381, B_382, D_383]: (~r2_hidden(C_381, k2_zfmisc_1(B_382, D_383)) | ~r1_xboole_0(B_382, B_382))), inference(resolution, [status(thm)], [c_6390, c_5997])).
% 17.07/9.34  tff(c_6436, plain, (![B_384, D_385]: (~r1_xboole_0(B_384, B_384) | k2_zfmisc_1(B_384, D_385)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_6421])).
% 17.07/9.34  tff(c_6475, plain, (![D_385]: (k2_zfmisc_1(k1_xboole_0, D_385)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6376, c_6436])).
% 17.07/9.34  tff(c_5652, plain, (![A_323, B_324]: (k4_xboole_0(A_323, B_324)=k1_xboole_0 | ~r1_tarski(A_323, B_324))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.07/9.34  tff(c_5664, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_5543, c_5652])).
% 17.07/9.34  tff(c_7483, plain, (![A_453, C_454, B_455, D_456]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_453, C_454), B_455), k2_zfmisc_1(A_453, k4_xboole_0(B_455, D_456)))=k4_xboole_0(k2_zfmisc_1(A_453, B_455), k2_zfmisc_1(C_454, D_456)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.07/9.34  tff(c_28, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.07/9.34  tff(c_5632, plain, (![A_319, B_320]: (k3_tarski(k2_tarski(A_319, B_320))=k2_xboole_0(A_319, B_320))), inference(cnfTransformation, [status(thm)], [f_85])).
% 17.07/9.34  tff(c_5708, plain, (![B_331, A_332]: (k3_tarski(k2_tarski(B_331, A_332))=k2_xboole_0(A_332, B_331))), inference(superposition, [status(thm), theory('equality')], [c_28, c_5632])).
% 17.07/9.34  tff(c_42, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_85])).
% 17.07/9.34  tff(c_5714, plain, (![B_331, A_332]: (k2_xboole_0(B_331, A_332)=k2_xboole_0(A_332, B_331))), inference(superposition, [status(thm), theory('equality')], [c_5708, c_42])).
% 17.07/9.34  tff(c_34566, plain, (![A_893, B_894, D_895, C_896]: (k2_xboole_0(k2_zfmisc_1(A_893, k4_xboole_0(B_894, D_895)), k2_zfmisc_1(k4_xboole_0(A_893, C_896), B_894))=k4_xboole_0(k2_zfmisc_1(A_893, B_894), k2_zfmisc_1(C_896, D_895)))), inference(superposition, [status(thm), theory('equality')], [c_7483, c_5714])).
% 17.07/9.34  tff(c_35037, plain, (![B_894, D_895]: (k2_xboole_0(k2_zfmisc_1('#skF_3', k4_xboole_0(B_894, D_895)), k2_zfmisc_1(k1_xboole_0, B_894))=k4_xboole_0(k2_zfmisc_1('#skF_3', B_894), k2_zfmisc_1('#skF_5', D_895)))), inference(superposition, [status(thm), theory('equality')], [c_5664, c_34566])).
% 17.07/9.34  tff(c_61239, plain, (![B_1195, D_1196]: (k4_xboole_0(k2_zfmisc_1('#skF_3', B_1195), k2_zfmisc_1('#skF_5', D_1196))=k2_zfmisc_1('#skF_3', k4_xboole_0(B_1195, D_1196)))), inference(demodulation, [status(thm), theory('equality')], [c_5569, c_6475, c_35037])).
% 17.07/9.34  tff(c_5663, plain, (k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_5652])).
% 17.07/9.34  tff(c_61420, plain, (k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_61239, c_5663])).
% 17.07/9.34  tff(c_61935, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_61420, c_44])).
% 17.07/9.34  tff(c_62055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6042, c_5651, c_61935])).
% 17.07/9.34  tff(c_62058, plain, (![C_1197]: (~r2_hidden(C_1197, '#skF_3'))), inference(splitRight, [status(thm)], [c_5994])).
% 17.07/9.34  tff(c_62063, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10, c_62058])).
% 17.07/9.34  tff(c_48, plain, (![B_54]: (k2_zfmisc_1(k1_xboole_0, B_54)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 17.07/9.34  tff(c_62092, plain, (![B_54]: (k2_zfmisc_1('#skF_3', B_54)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62063, c_62063, c_48])).
% 17.07/9.34  tff(c_62096, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62063, c_58])).
% 17.07/9.34  tff(c_62211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62092, c_62096])).
% 17.07/9.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.07/9.34  
% 17.07/9.34  Inference rules
% 17.07/9.34  ----------------------
% 17.07/9.34  #Ref     : 0
% 17.07/9.34  #Sup     : 15995
% 17.07/9.34  #Fact    : 0
% 17.07/9.34  #Define  : 0
% 17.07/9.34  #Split   : 6
% 17.07/9.34  #Chain   : 0
% 17.07/9.34  #Close   : 0
% 17.07/9.34  
% 17.07/9.34  Ordering : KBO
% 17.07/9.34  
% 17.07/9.34  Simplification rules
% 17.07/9.34  ----------------------
% 17.07/9.34  #Subsume      : 5257
% 17.07/9.34  #Demod        : 10389
% 17.07/9.34  #Tautology    : 7528
% 17.07/9.34  #SimpNegUnit  : 224
% 17.07/9.34  #BackRed      : 25
% 17.07/9.34  
% 17.07/9.34  #Partial instantiations: 0
% 17.07/9.34  #Strategies tried      : 1
% 17.07/9.34  
% 17.07/9.34  Timing (in seconds)
% 17.07/9.34  ----------------------
% 17.07/9.34  Preprocessing        : 0.33
% 17.07/9.34  Parsing              : 0.18
% 17.07/9.34  CNF conversion       : 0.02
% 17.07/9.34  Main loop            : 8.23
% 17.07/9.34  Inferencing          : 1.30
% 17.07/9.34  Reduction            : 4.45
% 17.07/9.34  Demodulation         : 3.84
% 17.07/9.34  BG Simplification    : 0.14
% 17.07/9.34  Subsumption          : 2.07
% 17.07/9.34  Abstraction          : 0.27
% 17.07/9.34  MUC search           : 0.00
% 17.07/9.34  Cooper               : 0.00
% 17.07/9.34  Total                : 8.61
% 17.07/9.34  Index Insertion      : 0.00
% 17.07/9.34  Index Deletion       : 0.00
% 17.07/9.34  Index Matching       : 0.00
% 17.07/9.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
