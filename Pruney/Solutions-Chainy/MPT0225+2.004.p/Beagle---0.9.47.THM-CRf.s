%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:31 EST 2020

% Result     : Theorem 5.22s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 175 expanded)
%              Number of leaves         :   37 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 243 expanded)
%              Number of equality atoms :   68 ( 152 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_93,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_110,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_112,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_28,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4813,plain,(
    ! [A_286,B_287] : r1_xboole_0(k4_xboole_0(A_286,B_287),B_287) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4816,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4813])).

tff(c_18,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4954,plain,(
    ! [A_315,B_316] :
      ( k4_xboole_0(A_315,B_316) = k1_xboole_0
      | ~ r1_tarski(A_315,B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4962,plain,(
    ! [B_14] : k4_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_4954])).

tff(c_5019,plain,(
    ! [A_326,B_327] : k4_xboole_0(A_326,k4_xboole_0(A_326,B_327)) = k3_xboole_0(A_326,B_327) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5040,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5019])).

tff(c_5044,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4962,c_5040])).

tff(c_5202,plain,(
    ! [A_334,B_335,C_336] :
      ( ~ r1_xboole_0(A_334,B_335)
      | ~ r2_hidden(C_336,k3_xboole_0(A_334,B_335)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5208,plain,(
    ! [A_21,C_336] :
      ( ~ r1_xboole_0(A_21,k1_xboole_0)
      | ~ r2_hidden(C_336,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5044,c_5202])).

tff(c_5229,plain,(
    ! [C_336] : ~ r2_hidden(C_336,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4816,c_5208])).

tff(c_106,plain,(
    ! [A_50,B_51] : r1_xboole_0(k4_xboole_0(A_50,B_51),B_51) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_109,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_106])).

tff(c_4588,plain,(
    ! [A_264,B_265] :
      ( k4_xboole_0(A_264,B_265) = k1_xboole_0
      | ~ r1_tarski(A_264,B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4596,plain,(
    ! [B_14] : k4_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_4588])).

tff(c_4699,plain,(
    ! [A_278,B_279] : k4_xboole_0(A_278,k4_xboole_0(A_278,B_279)) = k3_xboole_0(A_278,B_279) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4723,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4699])).

tff(c_4728,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4596,c_4723])).

tff(c_4760,plain,(
    ! [A_281,B_282,C_283] :
      ( ~ r1_xboole_0(A_281,B_282)
      | ~ r2_hidden(C_283,k3_xboole_0(A_281,B_282)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4763,plain,(
    ! [A_21,C_283] :
      ( ~ r1_xboole_0(A_21,k1_xboole_0)
      | ~ r2_hidden(C_283,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4728,c_4760])).

tff(c_4782,plain,(
    ! [C_283] : ~ r2_hidden(C_283,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_4763])).

tff(c_74,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_90,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_192,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k1_xboole_0
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_200,plain,(
    ! [B_14] : k4_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_331,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k4_xboole_0(A_97,B_98)) = k3_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_352,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_331])).

tff(c_370,plain,(
    ! [A_102] : k3_xboole_0(A_102,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_352])).

tff(c_24,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_375,plain,(
    ! [A_102] : k5_xboole_0(A_102,k1_xboole_0) = k4_xboole_0(A_102,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_24])).

tff(c_404,plain,(
    ! [A_102] : k5_xboole_0(A_102,k1_xboole_0) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_375])).

tff(c_70,plain,(
    ! [A_44,B_45] :
      ( r1_xboole_0(k1_tarski(A_44),k1_tarski(B_45))
      | B_45 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_248,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,k3_xboole_0(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_923,plain,(
    ! [A_145,B_146,B_147] :
      ( ~ r1_xboole_0(A_145,B_146)
      | r1_xboole_0(k3_xboole_0(A_145,B_146),B_147) ) ),
    inference(resolution,[status(thm)],[c_8,c_248])).

tff(c_34,plain,(
    ! [A_24] :
      ( ~ r1_xboole_0(A_24,A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_979,plain,(
    ! [A_154,B_155] :
      ( k3_xboole_0(A_154,B_155) = k1_xboole_0
      | ~ r1_xboole_0(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_923,c_34])).

tff(c_1847,plain,(
    ! [A_200,B_201] :
      ( k3_xboole_0(k1_tarski(A_200),k1_tarski(B_201)) = k1_xboole_0
      | B_201 = A_200 ) ),
    inference(resolution,[status(thm)],[c_70,c_979])).

tff(c_1892,plain,(
    ! [A_200,B_201] :
      ( k4_xboole_0(k1_tarski(A_200),k1_tarski(B_201)) = k5_xboole_0(k1_tarski(A_200),k1_xboole_0)
      | B_201 = A_200 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_24])).

tff(c_4480,plain,(
    ! [A_258,B_259] :
      ( k4_xboole_0(k1_tarski(A_258),k1_tarski(B_259)) = k1_tarski(A_258)
      | B_259 = A_258 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_1892])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_179,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_4543,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4480,c_179])).

tff(c_4569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_4543])).

tff(c_4571,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4570,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4633,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4596,c_4570,c_4570,c_76])).

tff(c_4634,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4633])).

tff(c_4652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4571,c_4634])).

tff(c_4653,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4633])).

tff(c_62,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_155,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    ! [E_33,A_27,C_29] : r2_hidden(E_33,k1_enumset1(A_27,E_33,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_173,plain,(
    ! [A_68,B_69] : r2_hidden(A_68,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_42])).

tff(c_176,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_173])).

tff(c_4664,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4653,c_176])).

tff(c_4786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4782,c_4664])).

tff(c_4787,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4788,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4880,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4787,c_4787,c_4788,c_78])).

tff(c_36,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4884,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4880,c_36])).

tff(c_4902,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4884,c_34])).

tff(c_4861,plain,(
    ! [A_300,B_301] : k1_enumset1(A_300,A_300,B_301) = k2_tarski(A_300,B_301) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    ! [E_33,A_27,B_28] : r2_hidden(E_33,k1_enumset1(A_27,B_28,E_33)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4888,plain,(
    ! [B_302,A_303] : r2_hidden(B_302,k2_tarski(A_303,B_302)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4861,c_40])).

tff(c_4891,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_4888])).

tff(c_4915,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4902,c_4891])).

tff(c_5233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5229,c_4915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:08:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.22/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/1.99  
% 5.22/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/1.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_1
% 5.22/1.99  
% 5.22/1.99  %Foreground sorts:
% 5.22/1.99  
% 5.22/1.99  
% 5.22/1.99  %Background operators:
% 5.22/1.99  
% 5.22/1.99  
% 5.22/1.99  %Foreground operators:
% 5.22/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.22/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.22/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.22/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.22/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.22/1.99  tff('#skF_7', type, '#skF_7': $i).
% 5.22/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.22/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.22/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.22/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.22/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.22/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.22/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.22/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.22/1.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.22/1.99  tff('#skF_8', type, '#skF_8': $i).
% 5.22/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.22/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.22/1.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.22/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.22/1.99  
% 5.22/2.01  tff(f_77, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.22/2.01  tff(f_93, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.22/2.01  tff(f_65, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.22/2.01  tff(f_69, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.22/2.01  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.22/2.01  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.22/2.01  tff(f_127, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 5.22/2.01  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.22/2.01  tff(f_121, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 5.22/2.01  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.22/2.01  tff(f_91, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.22/2.01  tff(f_110, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.22/2.01  tff(f_112, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.22/2.01  tff(f_108, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.22/2.01  tff(c_28, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.22/2.01  tff(c_4813, plain, (![A_286, B_287]: (r1_xboole_0(k4_xboole_0(A_286, B_287), B_287))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.22/2.01  tff(c_4816, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4813])).
% 5.22/2.01  tff(c_18, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.22/2.01  tff(c_4954, plain, (![A_315, B_316]: (k4_xboole_0(A_315, B_316)=k1_xboole_0 | ~r1_tarski(A_315, B_316))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.22/2.01  tff(c_4962, plain, (![B_14]: (k4_xboole_0(B_14, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_4954])).
% 5.22/2.01  tff(c_5019, plain, (![A_326, B_327]: (k4_xboole_0(A_326, k4_xboole_0(A_326, B_327))=k3_xboole_0(A_326, B_327))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.22/2.01  tff(c_5040, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_5019])).
% 5.22/2.01  tff(c_5044, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4962, c_5040])).
% 5.22/2.01  tff(c_5202, plain, (![A_334, B_335, C_336]: (~r1_xboole_0(A_334, B_335) | ~r2_hidden(C_336, k3_xboole_0(A_334, B_335)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.22/2.01  tff(c_5208, plain, (![A_21, C_336]: (~r1_xboole_0(A_21, k1_xboole_0) | ~r2_hidden(C_336, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5044, c_5202])).
% 5.22/2.01  tff(c_5229, plain, (![C_336]: (~r2_hidden(C_336, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4816, c_5208])).
% 5.22/2.01  tff(c_106, plain, (![A_50, B_51]: (r1_xboole_0(k4_xboole_0(A_50, B_51), B_51))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.22/2.01  tff(c_109, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_106])).
% 5.22/2.01  tff(c_4588, plain, (![A_264, B_265]: (k4_xboole_0(A_264, B_265)=k1_xboole_0 | ~r1_tarski(A_264, B_265))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.22/2.01  tff(c_4596, plain, (![B_14]: (k4_xboole_0(B_14, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_4588])).
% 5.22/2.01  tff(c_4699, plain, (![A_278, B_279]: (k4_xboole_0(A_278, k4_xboole_0(A_278, B_279))=k3_xboole_0(A_278, B_279))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.22/2.01  tff(c_4723, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4699])).
% 5.22/2.01  tff(c_4728, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4596, c_4723])).
% 5.22/2.01  tff(c_4760, plain, (![A_281, B_282, C_283]: (~r1_xboole_0(A_281, B_282) | ~r2_hidden(C_283, k3_xboole_0(A_281, B_282)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.22/2.01  tff(c_4763, plain, (![A_21, C_283]: (~r1_xboole_0(A_21, k1_xboole_0) | ~r2_hidden(C_283, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4728, c_4760])).
% 5.22/2.01  tff(c_4782, plain, (![C_283]: (~r2_hidden(C_283, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_4763])).
% 5.22/2.01  tff(c_74, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.22/2.01  tff(c_90, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_74])).
% 5.22/2.01  tff(c_192, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k1_xboole_0 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.22/2.01  tff(c_200, plain, (![B_14]: (k4_xboole_0(B_14, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_192])).
% 5.22/2.01  tff(c_331, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k4_xboole_0(A_97, B_98))=k3_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.22/2.01  tff(c_352, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_331])).
% 5.22/2.01  tff(c_370, plain, (![A_102]: (k3_xboole_0(A_102, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_352])).
% 5.22/2.01  tff(c_24, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.22/2.01  tff(c_375, plain, (![A_102]: (k5_xboole_0(A_102, k1_xboole_0)=k4_xboole_0(A_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_370, c_24])).
% 5.22/2.01  tff(c_404, plain, (![A_102]: (k5_xboole_0(A_102, k1_xboole_0)=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_375])).
% 5.22/2.01  tff(c_70, plain, (![A_44, B_45]: (r1_xboole_0(k1_tarski(A_44), k1_tarski(B_45)) | B_45=A_44)), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.22/2.01  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.22/2.01  tff(c_248, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, k3_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.22/2.01  tff(c_923, plain, (![A_145, B_146, B_147]: (~r1_xboole_0(A_145, B_146) | r1_xboole_0(k3_xboole_0(A_145, B_146), B_147))), inference(resolution, [status(thm)], [c_8, c_248])).
% 5.22/2.01  tff(c_34, plain, (![A_24]: (~r1_xboole_0(A_24, A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.22/2.01  tff(c_979, plain, (![A_154, B_155]: (k3_xboole_0(A_154, B_155)=k1_xboole_0 | ~r1_xboole_0(A_154, B_155))), inference(resolution, [status(thm)], [c_923, c_34])).
% 5.22/2.01  tff(c_1847, plain, (![A_200, B_201]: (k3_xboole_0(k1_tarski(A_200), k1_tarski(B_201))=k1_xboole_0 | B_201=A_200)), inference(resolution, [status(thm)], [c_70, c_979])).
% 5.22/2.01  tff(c_1892, plain, (![A_200, B_201]: (k4_xboole_0(k1_tarski(A_200), k1_tarski(B_201))=k5_xboole_0(k1_tarski(A_200), k1_xboole_0) | B_201=A_200)), inference(superposition, [status(thm), theory('equality')], [c_1847, c_24])).
% 5.22/2.01  tff(c_4480, plain, (![A_258, B_259]: (k4_xboole_0(k1_tarski(A_258), k1_tarski(B_259))=k1_tarski(A_258) | B_259=A_258)), inference(demodulation, [status(thm), theory('equality')], [c_404, c_1892])).
% 5.22/2.01  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.22/2.01  tff(c_179, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 5.22/2.01  tff(c_4543, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4480, c_179])).
% 5.22/2.01  tff(c_4569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_4543])).
% 5.22/2.01  tff(c_4571, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 5.22/2.01  tff(c_4570, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_72])).
% 5.22/2.01  tff(c_76, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.22/2.01  tff(c_4633, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4596, c_4570, c_4570, c_76])).
% 5.22/2.01  tff(c_4634, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_4633])).
% 5.22/2.01  tff(c_4652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4571, c_4634])).
% 5.22/2.01  tff(c_4653, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4633])).
% 5.22/2.01  tff(c_62, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.22/2.01  tff(c_155, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.22/2.01  tff(c_42, plain, (![E_33, A_27, C_29]: (r2_hidden(E_33, k1_enumset1(A_27, E_33, C_29)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.22/2.01  tff(c_173, plain, (![A_68, B_69]: (r2_hidden(A_68, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_42])).
% 5.22/2.01  tff(c_176, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_173])).
% 5.22/2.01  tff(c_4664, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4653, c_176])).
% 5.22/2.01  tff(c_4786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4782, c_4664])).
% 5.22/2.01  tff(c_4787, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_74])).
% 5.22/2.01  tff(c_4788, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 5.22/2.01  tff(c_78, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.22/2.01  tff(c_4880, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4787, c_4787, c_4788, c_78])).
% 5.22/2.01  tff(c_36, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.22/2.01  tff(c_4884, plain, (r1_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4880, c_36])).
% 5.22/2.01  tff(c_4902, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_4884, c_34])).
% 5.22/2.01  tff(c_4861, plain, (![A_300, B_301]: (k1_enumset1(A_300, A_300, B_301)=k2_tarski(A_300, B_301))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.22/2.01  tff(c_40, plain, (![E_33, A_27, B_28]: (r2_hidden(E_33, k1_enumset1(A_27, B_28, E_33)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.22/2.01  tff(c_4888, plain, (![B_302, A_303]: (r2_hidden(B_302, k2_tarski(A_303, B_302)))), inference(superposition, [status(thm), theory('equality')], [c_4861, c_40])).
% 5.22/2.01  tff(c_4891, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_4888])).
% 5.22/2.01  tff(c_4915, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4902, c_4891])).
% 5.22/2.01  tff(c_5233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5229, c_4915])).
% 5.22/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.01  
% 5.22/2.01  Inference rules
% 5.22/2.01  ----------------------
% 5.22/2.01  #Ref     : 0
% 5.22/2.01  #Sup     : 1242
% 5.22/2.01  #Fact    : 0
% 5.22/2.01  #Define  : 0
% 5.22/2.01  #Split   : 3
% 5.22/2.01  #Chain   : 0
% 5.22/2.01  #Close   : 0
% 5.22/2.01  
% 5.22/2.01  Ordering : KBO
% 5.22/2.01  
% 5.22/2.01  Simplification rules
% 5.22/2.01  ----------------------
% 5.22/2.01  #Subsume      : 164
% 5.22/2.01  #Demod        : 876
% 5.22/2.01  #Tautology    : 797
% 5.22/2.01  #SimpNegUnit  : 29
% 5.22/2.01  #BackRed      : 4
% 5.22/2.01  
% 5.22/2.01  #Partial instantiations: 0
% 5.22/2.01  #Strategies tried      : 1
% 5.22/2.01  
% 5.22/2.01  Timing (in seconds)
% 5.22/2.01  ----------------------
% 5.22/2.01  Preprocessing        : 0.35
% 5.22/2.01  Parsing              : 0.18
% 5.22/2.01  CNF conversion       : 0.03
% 5.22/2.01  Main loop            : 0.89
% 5.22/2.01  Inferencing          : 0.28
% 5.22/2.01  Reduction            : 0.36
% 5.22/2.01  Demodulation         : 0.28
% 5.22/2.01  BG Simplification    : 0.03
% 5.22/2.02  Subsumption          : 0.16
% 5.22/2.02  Abstraction          : 0.04
% 5.22/2.02  MUC search           : 0.00
% 5.22/2.02  Cooper               : 0.00
% 5.22/2.02  Total                : 1.28
% 5.22/2.02  Index Insertion      : 0.00
% 5.22/2.02  Index Deletion       : 0.00
% 5.22/2.02  Index Matching       : 0.00
% 5.22/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
