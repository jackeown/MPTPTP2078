%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:53 EST 2020

% Result     : Theorem 17.52s
% Output     : CNFRefutation 17.52s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 421 expanded)
%              Number of leaves         :   37 ( 154 expanded)
%              Depth                    :   16
%              Number of atoms          :  204 ( 684 expanded)
%              Number of equality atoms :  139 ( 496 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_226,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_68,plain,(
    ! [C_45,A_43,B_44] : r1_tarski(k1_tarski(C_45),k1_enumset1(A_43,B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_232,plain,(
    ! [B_71,A_70] : r1_tarski(k1_tarski(B_71),k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_68])).

tff(c_82,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_258,plain,(
    ! [A_82,B_83] :
      ( k2_xboole_0(A_82,B_83) = B_83
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_314,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_86,c_258])).

tff(c_44,plain,(
    ! [A_27,B_28] : k3_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_338,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_44])).

tff(c_84,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1839,plain,(
    ! [A_175,B_176,C_177] : k3_xboole_0(k3_xboole_0(A_175,B_176),C_177) = k3_xboole_0(A_175,k3_xboole_0(B_176,C_177)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9133,plain,(
    ! [C_335,A_336,B_337] : k3_xboole_0(C_335,k3_xboole_0(A_336,B_337)) = k3_xboole_0(A_336,k3_xboole_0(B_337,C_335)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_4])).

tff(c_10408,plain,(
    ! [A_345] : k3_xboole_0(A_345,k1_tarski('#skF_7')) = k3_xboole_0('#skF_6',k3_xboole_0(A_345,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_9133])).

tff(c_10752,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_7')) = k3_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_10408])).

tff(c_10843,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10752])).

tff(c_10959,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_6')) = k4_xboole_0('#skF_4',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10843,c_46])).

tff(c_11006,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_7')) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10959])).

tff(c_76,plain,(
    ! [B_48,A_47] :
      ( ~ r2_hidden(B_48,A_47)
      | k4_xboole_0(A_47,k1_tarski(B_48)) != A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_11059,plain,
    ( ~ r2_hidden('#skF_7','#skF_4')
    | k4_xboole_0('#skF_4','#skF_6') != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11006,c_76])).

tff(c_11090,plain,(
    k4_xboole_0('#skF_4','#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_11059])).

tff(c_30,plain,(
    ! [A_16] : k3_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3308,plain,(
    ! [A_229,B_230,C_231] :
      ( r2_hidden('#skF_2'(A_229,B_230,C_231),A_229)
      | r2_hidden('#skF_3'(A_229,B_230,C_231),C_231)
      | k4_xboole_0(A_229,B_230) = C_231 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_10,B_11,C_12] :
      ( ~ r2_hidden('#skF_2'(A_10,B_11,C_12),B_11)
      | r2_hidden('#skF_3'(A_10,B_11,C_12),C_12)
      | k4_xboole_0(A_10,B_11) = C_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_23703,plain,(
    ! [A_442,C_443] :
      ( r2_hidden('#skF_3'(A_442,A_442,C_443),C_443)
      | k4_xboole_0(A_442,A_442) = C_443 ) ),
    inference(resolution,[status(thm)],[c_3308,c_26])).

tff(c_50,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    ! [A_43,B_44,C_45] : r1_tarski(k1_xboole_0,k1_enumset1(A_43,B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_240,plain,(
    ! [A_72,B_73] : r1_tarski(k1_xboole_0,k2_tarski(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_74])).

tff(c_242,plain,(
    ! [A_33] : r1_tarski(k1_xboole_0,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_240])).

tff(c_515,plain,(
    ! [A_92] : k2_xboole_0(k1_xboole_0,k1_tarski(A_92)) = k1_tarski(A_92) ),
    inference(resolution,[status(thm)],[c_242,c_258])).

tff(c_524,plain,(
    ! [A_92] : k3_xboole_0(k1_xboole_0,k1_tarski(A_92)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_44])).

tff(c_606,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_621,plain,(
    ! [A_92] : k4_xboole_0(k1_xboole_0,k1_tarski(A_92)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_606])).

tff(c_788,plain,(
    ! [B_109,A_110] :
      ( ~ r2_hidden(B_109,A_110)
      | k4_xboole_0(A_110,k1_tarski(B_109)) != A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_791,plain,(
    ! [A_92] :
      ( ~ r2_hidden(A_92,k1_xboole_0)
      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_788])).

tff(c_819,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_791])).

tff(c_921,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(A_125,k1_tarski(B_126)) = A_125
      | r2_hidden(B_126,A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_937,plain,(
    ! [B_126] :
      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | r2_hidden(B_126,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_621])).

tff(c_961,plain,(
    ! [B_126] : r2_hidden(B_126,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_937])).

tff(c_986,plain,(
    ! [B_131] : r2_hidden(B_131,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_937])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1006,plain,(
    ! [B_133] : ~ r2_hidden(k1_xboole_0,B_133) ),
    inference(resolution,[status(thm)],[c_986,c_2])).

tff(c_1011,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_961,c_1006])).

tff(c_1012,plain,(
    ! [A_92] : ~ r2_hidden(A_92,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_23797,plain,(
    ! [A_444] : k4_xboole_0(A_444,A_444) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23703,c_1012])).

tff(c_48,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_23922,plain,(
    ! [A_444] : k4_xboole_0(A_444,k1_xboole_0) = k3_xboole_0(A_444,A_444) ),
    inference(superposition,[status(thm),theory(equality)],[c_23797,c_48])).

tff(c_23970,plain,(
    ! [A_444] : k4_xboole_0(A_444,k1_xboole_0) = A_444 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_23922])).

tff(c_80,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_377,plain,(
    ! [B_85,A_86,C_87] : r1_tarski(k1_tarski(B_85),k1_enumset1(A_86,B_85,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26800,plain,(
    ! [B_464,A_465,C_466] : k2_xboole_0(k1_tarski(B_464),k1_enumset1(A_465,B_464,C_466)) = k1_enumset1(A_465,B_464,C_466) ),
    inference(resolution,[status(thm)],[c_377,c_38])).

tff(c_1945,plain,(
    ! [A_16,C_177] : k3_xboole_0(A_16,k3_xboole_0(A_16,C_177)) = k3_xboole_0(A_16,C_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1839])).

tff(c_11916,plain,(
    ! [A_350,B_351,C_352] : k3_xboole_0(A_350,k3_xboole_0(k2_xboole_0(A_350,B_351),C_352)) = k3_xboole_0(A_350,C_352) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1839])).

tff(c_12803,plain,(
    ! [C_355] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_355)) = k3_xboole_0('#skF_4',C_355) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_11916])).

tff(c_9802,plain,(
    ! [A_16,C_335] : k3_xboole_0(A_16,k3_xboole_0(A_16,C_335)) = k3_xboole_0(C_335,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_9133])).

tff(c_12816,plain,(
    ! [C_355] : k3_xboole_0(k3_xboole_0('#skF_5',C_355),'#skF_4') = k3_xboole_0('#skF_4',k3_xboole_0('#skF_4',C_355)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12803,c_9802])).

tff(c_19122,plain,(
    ! [C_409] : k3_xboole_0(k3_xboole_0('#skF_5',C_409),'#skF_4') = k3_xboole_0('#skF_4',C_409) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1945,c_12816])).

tff(c_19372,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_19122])).

tff(c_138,plain,(
    ! [B_61,A_62] : k3_xboole_0(B_61,A_62) = k3_xboole_0(A_62,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_25,B_26] : r1_tarski(k3_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_153,plain,(
    ! [B_61,A_62] : r1_tarski(k3_xboole_0(B_61,A_62),A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_42])).

tff(c_2092,plain,(
    ! [A_181,B_182,C_183] : r1_tarski(k3_xboole_0(A_181,k3_xboole_0(B_182,C_183)),C_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_153])).

tff(c_2590,plain,(
    ! [A_198,A_199,B_200] : r1_tarski(k3_xboole_0(A_198,A_199),k2_xboole_0(A_199,B_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2092])).

tff(c_2658,plain,(
    ! [B_4,A_3,B_200] : r1_tarski(k3_xboole_0(B_4,A_3),k2_xboole_0(B_4,B_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2590])).

tff(c_19522,plain,(
    ! [B_200] : r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k2_xboole_0(k1_tarski('#skF_7'),B_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19372,c_2658])).

tff(c_43982,plain,(
    ! [A_672,C_673] : r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k1_enumset1(A_672,'#skF_7',C_673)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26800,c_19522])).

tff(c_58,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k1_enumset1(A_43,B_44,C_45) = D_46
      | k2_tarski(A_43,C_45) = D_46
      | k2_tarski(B_44,C_45) = D_46
      | k2_tarski(A_43,B_44) = D_46
      | k1_tarski(C_45) = D_46
      | k1_tarski(B_44) = D_46
      | k1_tarski(A_43) = D_46
      | k1_xboole_0 = D_46
      | ~ r1_tarski(D_46,k1_enumset1(A_43,B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_43987,plain,(
    ! [A_672,C_673] :
      ( k1_enumset1(A_672,'#skF_7',C_673) = k3_xboole_0('#skF_4','#skF_6')
      | k3_xboole_0('#skF_4','#skF_6') = k2_tarski(A_672,C_673)
      | k3_xboole_0('#skF_4','#skF_6') = k2_tarski('#skF_7',C_673)
      | k3_xboole_0('#skF_4','#skF_6') = k2_tarski(A_672,'#skF_7')
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski(C_673)
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski(A_672)
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_43982,c_58])).

tff(c_44000,plain,(
    ! [A_672,C_673] :
      ( k1_enumset1(A_672,'#skF_7',C_673) = k3_xboole_0('#skF_4','#skF_6')
      | k3_xboole_0('#skF_4','#skF_6') = k2_tarski(A_672,C_673)
      | k3_xboole_0('#skF_4','#skF_6') = k2_tarski('#skF_7',C_673)
      | k3_xboole_0('#skF_4','#skF_6') = k2_tarski(A_672,'#skF_7')
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski(C_673)
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski(A_672)
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_43987])).

tff(c_44409,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44000])).

tff(c_44616,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_44409,c_46])).

tff(c_44686,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23970,c_44616])).

tff(c_44688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11090,c_44686])).

tff(c_44690,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44000])).

tff(c_52,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_27831,plain,(
    ! [C_482,A_483,B_484] : k2_xboole_0(k1_tarski(C_482),k1_enumset1(A_483,B_484,C_482)) = k1_enumset1(A_483,B_484,C_482) ),
    inference(resolution,[status(thm)],[c_68,c_258])).

tff(c_44692,plain,(
    ! [A_681,B_682] : r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k1_enumset1(A_681,B_682,'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27831,c_19522])).

tff(c_44706,plain,(
    ! [A_34] : r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k2_tarski(A_34,'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_44692])).

tff(c_4996,plain,(
    ! [A_284,B_285,C_286,D_287] :
      ( k1_enumset1(A_284,B_285,C_286) = D_287
      | k2_tarski(A_284,C_286) = D_287
      | k2_tarski(B_285,C_286) = D_287
      | k2_tarski(A_284,B_285) = D_287
      | k1_tarski(C_286) = D_287
      | k1_tarski(B_285) = D_287
      | k1_tarski(A_284) = D_287
      | k1_xboole_0 = D_287
      | ~ r1_tarski(D_287,k1_enumset1(A_284,B_285,C_286)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5050,plain,(
    ! [A_34,B_35,D_287] :
      ( k1_enumset1(A_34,A_34,B_35) = D_287
      | k2_tarski(A_34,B_35) = D_287
      | k2_tarski(A_34,B_35) = D_287
      | k2_tarski(A_34,A_34) = D_287
      | k1_tarski(B_35) = D_287
      | k1_tarski(A_34) = D_287
      | k1_tarski(A_34) = D_287
      | k1_xboole_0 = D_287
      | ~ r1_tarski(D_287,k2_tarski(A_34,B_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4996])).

tff(c_51890,plain,(
    ! [A_776,B_777,D_778] :
      ( k2_tarski(A_776,B_777) = D_778
      | k2_tarski(A_776,B_777) = D_778
      | k2_tarski(A_776,B_777) = D_778
      | k1_tarski(A_776) = D_778
      | k1_tarski(B_777) = D_778
      | k1_tarski(A_776) = D_778
      | k1_tarski(A_776) = D_778
      | k1_xboole_0 = D_778
      | ~ r1_tarski(D_778,k2_tarski(A_776,B_777)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_5050])).

tff(c_51904,plain,(
    ! [A_34] :
      ( k3_xboole_0('#skF_4','#skF_6') = k2_tarski(A_34,'#skF_7')
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski(A_34)
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44706,c_51890])).

tff(c_52466,plain,(
    ! [A_780] :
      ( k3_xboole_0('#skF_4','#skF_6') = k2_tarski(A_780,'#skF_7')
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski(A_780) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44690,c_80,c_51904])).

tff(c_386,plain,(
    ! [A_88,B_89] : k2_xboole_0(k3_xboole_0(A_88,B_89),A_88) = A_88 ),
    inference(resolution,[status(thm)],[c_42,c_258])).

tff(c_7094,plain,(
    ! [A_318,B_319] : k3_xboole_0(k3_xboole_0(A_318,B_319),A_318) = k3_xboole_0(A_318,B_319) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_44])).

tff(c_7676,plain,(
    ! [A_324,B_325] : k3_xboole_0(k3_xboole_0(A_324,B_325),B_325) = k3_xboole_0(B_325,A_324) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7094])).

tff(c_7930,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_7676])).

tff(c_8021,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_7930])).

tff(c_159,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_84])).

tff(c_6655,plain,(
    ! [A_311,B_312,C_313] : r1_tarski(k3_xboole_0(A_311,k3_xboole_0(B_312,C_313)),k3_xboole_0(A_311,B_312)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_42])).

tff(c_6771,plain,(
    ! [C_313] : r1_tarski(k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_313)),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_6655])).

tff(c_8041,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_4'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8021,c_6771])).

tff(c_8135,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8041])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( B_19 = A_18
      | ~ r1_tarski(B_19,A_18)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8280,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r1_tarski(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_8135,c_32])).

tff(c_8286,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8280])).

tff(c_52640,plain,(
    ! [A_780] :
      ( ~ r1_tarski(k1_tarski('#skF_7'),k2_tarski(A_780,'#skF_7'))
      | k3_xboole_0('#skF_4','#skF_6') = k1_tarski(A_780) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52466,c_8286])).

tff(c_52784,plain,(
    ! [A_781] : k3_xboole_0('#skF_4','#skF_6') = k1_tarski(A_781) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_52640])).

tff(c_53071,plain,(
    ! [A_781] : k1_tarski(A_781) != k1_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_52784,c_80])).

tff(c_53912,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_53071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.52/9.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.52/9.95  
% 17.52/9.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.52/9.96  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 17.52/9.96  
% 17.52/9.96  %Foreground sorts:
% 17.52/9.96  
% 17.52/9.96  
% 17.52/9.96  %Background operators:
% 17.52/9.96  
% 17.52/9.96  
% 17.52/9.96  %Foreground operators:
% 17.52/9.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.52/9.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.52/9.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.52/9.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.52/9.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.52/9.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.52/9.96  tff('#skF_7', type, '#skF_7': $i).
% 17.52/9.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.52/9.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.52/9.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.52/9.96  tff('#skF_5', type, '#skF_5': $i).
% 17.52/9.96  tff('#skF_6', type, '#skF_6': $i).
% 17.52/9.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.52/9.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.52/9.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.52/9.96  tff('#skF_4', type, '#skF_4': $i).
% 17.52/9.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.52/9.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.52/9.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.52/9.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.52/9.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.52/9.96  
% 17.52/9.98  tff(f_75, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 17.52/9.98  tff(f_106, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 17.52/9.98  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 17.52/9.98  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 17.52/9.98  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.52/9.98  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 17.52/9.98  tff(f_67, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 17.52/9.98  tff(f_63, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 17.52/9.98  tff(f_111, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 17.52/9.98  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 17.52/9.98  tff(f_49, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.52/9.98  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 17.52/9.98  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 17.52/9.98  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.52/9.98  tff(f_65, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 17.52/9.98  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.52/9.98  tff(c_226, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.52/9.98  tff(c_68, plain, (![C_45, A_43, B_44]: (r1_tarski(k1_tarski(C_45), k1_enumset1(A_43, B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.52/9.98  tff(c_232, plain, (![B_71, A_70]: (r1_tarski(k1_tarski(B_71), k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_68])).
% 17.52/9.98  tff(c_82, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 17.52/9.98  tff(c_46, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.52/9.98  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.52/9.98  tff(c_86, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 17.52/9.98  tff(c_258, plain, (![A_82, B_83]: (k2_xboole_0(A_82, B_83)=B_83 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.52/9.98  tff(c_314, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_86, c_258])).
% 17.52/9.98  tff(c_44, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k2_xboole_0(A_27, B_28))=A_27)), inference(cnfTransformation, [status(thm)], [f_67])).
% 17.52/9.98  tff(c_338, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_314, c_44])).
% 17.52/9.98  tff(c_84, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 17.52/9.98  tff(c_1839, plain, (![A_175, B_176, C_177]: (k3_xboole_0(k3_xboole_0(A_175, B_176), C_177)=k3_xboole_0(A_175, k3_xboole_0(B_176, C_177)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.52/9.98  tff(c_9133, plain, (![C_335, A_336, B_337]: (k3_xboole_0(C_335, k3_xboole_0(A_336, B_337))=k3_xboole_0(A_336, k3_xboole_0(B_337, C_335)))), inference(superposition, [status(thm), theory('equality')], [c_1839, c_4])).
% 17.52/9.98  tff(c_10408, plain, (![A_345]: (k3_xboole_0(A_345, k1_tarski('#skF_7'))=k3_xboole_0('#skF_6', k3_xboole_0(A_345, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_9133])).
% 17.52/9.98  tff(c_10752, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_7'))=k3_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_338, c_10408])).
% 17.52/9.98  tff(c_10843, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10752])).
% 17.52/9.98  tff(c_10959, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))=k4_xboole_0('#skF_4', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10843, c_46])).
% 17.52/9.98  tff(c_11006, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_7'))=k4_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10959])).
% 17.52/9.98  tff(c_76, plain, (![B_48, A_47]: (~r2_hidden(B_48, A_47) | k4_xboole_0(A_47, k1_tarski(B_48))!=A_47)), inference(cnfTransformation, [status(thm)], [f_111])).
% 17.52/9.98  tff(c_11059, plain, (~r2_hidden('#skF_7', '#skF_4') | k4_xboole_0('#skF_4', '#skF_6')!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11006, c_76])).
% 17.52/9.98  tff(c_11090, plain, (k4_xboole_0('#skF_4', '#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_11059])).
% 17.52/9.98  tff(c_30, plain, (![A_16]: (k3_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.52/9.98  tff(c_3308, plain, (![A_229, B_230, C_231]: (r2_hidden('#skF_2'(A_229, B_230, C_231), A_229) | r2_hidden('#skF_3'(A_229, B_230, C_231), C_231) | k4_xboole_0(A_229, B_230)=C_231)), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.52/9.98  tff(c_26, plain, (![A_10, B_11, C_12]: (~r2_hidden('#skF_2'(A_10, B_11, C_12), B_11) | r2_hidden('#skF_3'(A_10, B_11, C_12), C_12) | k4_xboole_0(A_10, B_11)=C_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.52/9.98  tff(c_23703, plain, (![A_442, C_443]: (r2_hidden('#skF_3'(A_442, A_442, C_443), C_443) | k4_xboole_0(A_442, A_442)=C_443)), inference(resolution, [status(thm)], [c_3308, c_26])).
% 17.52/9.98  tff(c_50, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.52/9.98  tff(c_74, plain, (![A_43, B_44, C_45]: (r1_tarski(k1_xboole_0, k1_enumset1(A_43, B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.52/9.98  tff(c_240, plain, (![A_72, B_73]: (r1_tarski(k1_xboole_0, k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_74])).
% 17.52/9.98  tff(c_242, plain, (![A_33]: (r1_tarski(k1_xboole_0, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_240])).
% 17.52/9.98  tff(c_515, plain, (![A_92]: (k2_xboole_0(k1_xboole_0, k1_tarski(A_92))=k1_tarski(A_92))), inference(resolution, [status(thm)], [c_242, c_258])).
% 17.52/9.98  tff(c_524, plain, (![A_92]: (k3_xboole_0(k1_xboole_0, k1_tarski(A_92))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_515, c_44])).
% 17.52/9.98  tff(c_606, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.52/9.98  tff(c_621, plain, (![A_92]: (k4_xboole_0(k1_xboole_0, k1_tarski(A_92))=k4_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_524, c_606])).
% 17.52/9.98  tff(c_788, plain, (![B_109, A_110]: (~r2_hidden(B_109, A_110) | k4_xboole_0(A_110, k1_tarski(B_109))!=A_110)), inference(cnfTransformation, [status(thm)], [f_111])).
% 17.52/9.98  tff(c_791, plain, (![A_92]: (~r2_hidden(A_92, k1_xboole_0) | k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_621, c_788])).
% 17.52/9.98  tff(c_819, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_791])).
% 17.52/9.98  tff(c_921, plain, (![A_125, B_126]: (k4_xboole_0(A_125, k1_tarski(B_126))=A_125 | r2_hidden(B_126, A_125))), inference(cnfTransformation, [status(thm)], [f_111])).
% 17.52/9.98  tff(c_937, plain, (![B_126]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | r2_hidden(B_126, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_921, c_621])).
% 17.52/9.98  tff(c_961, plain, (![B_126]: (r2_hidden(B_126, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_819, c_937])).
% 17.52/9.98  tff(c_986, plain, (![B_131]: (r2_hidden(B_131, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_819, c_937])).
% 17.52/9.98  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 17.52/9.98  tff(c_1006, plain, (![B_133]: (~r2_hidden(k1_xboole_0, B_133))), inference(resolution, [status(thm)], [c_986, c_2])).
% 17.52/9.98  tff(c_1011, plain, $false, inference(resolution, [status(thm)], [c_961, c_1006])).
% 17.52/9.98  tff(c_1012, plain, (![A_92]: (~r2_hidden(A_92, k1_xboole_0))), inference(splitRight, [status(thm)], [c_791])).
% 17.52/9.98  tff(c_23797, plain, (![A_444]: (k4_xboole_0(A_444, A_444)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23703, c_1012])).
% 17.52/9.98  tff(c_48, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.52/9.98  tff(c_23922, plain, (![A_444]: (k4_xboole_0(A_444, k1_xboole_0)=k3_xboole_0(A_444, A_444))), inference(superposition, [status(thm), theory('equality')], [c_23797, c_48])).
% 17.52/9.98  tff(c_23970, plain, (![A_444]: (k4_xboole_0(A_444, k1_xboole_0)=A_444)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_23922])).
% 17.52/9.98  tff(c_80, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 17.52/9.98  tff(c_377, plain, (![B_85, A_86, C_87]: (r1_tarski(k1_tarski(B_85), k1_enumset1(A_86, B_85, C_87)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.52/9.98  tff(c_38, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.52/9.98  tff(c_26800, plain, (![B_464, A_465, C_466]: (k2_xboole_0(k1_tarski(B_464), k1_enumset1(A_465, B_464, C_466))=k1_enumset1(A_465, B_464, C_466))), inference(resolution, [status(thm)], [c_377, c_38])).
% 17.52/9.98  tff(c_1945, plain, (![A_16, C_177]: (k3_xboole_0(A_16, k3_xboole_0(A_16, C_177))=k3_xboole_0(A_16, C_177))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1839])).
% 17.52/9.98  tff(c_11916, plain, (![A_350, B_351, C_352]: (k3_xboole_0(A_350, k3_xboole_0(k2_xboole_0(A_350, B_351), C_352))=k3_xboole_0(A_350, C_352))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1839])).
% 17.52/9.98  tff(c_12803, plain, (![C_355]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_355))=k3_xboole_0('#skF_4', C_355))), inference(superposition, [status(thm), theory('equality')], [c_314, c_11916])).
% 17.52/9.98  tff(c_9802, plain, (![A_16, C_335]: (k3_xboole_0(A_16, k3_xboole_0(A_16, C_335))=k3_xboole_0(C_335, A_16))), inference(superposition, [status(thm), theory('equality')], [c_30, c_9133])).
% 17.52/9.98  tff(c_12816, plain, (![C_355]: (k3_xboole_0(k3_xboole_0('#skF_5', C_355), '#skF_4')=k3_xboole_0('#skF_4', k3_xboole_0('#skF_4', C_355)))), inference(superposition, [status(thm), theory('equality')], [c_12803, c_9802])).
% 17.52/9.98  tff(c_19122, plain, (![C_409]: (k3_xboole_0(k3_xboole_0('#skF_5', C_409), '#skF_4')=k3_xboole_0('#skF_4', C_409))), inference(demodulation, [status(thm), theory('equality')], [c_1945, c_12816])).
% 17.52/9.98  tff(c_19372, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_84, c_19122])).
% 17.52/9.98  tff(c_138, plain, (![B_61, A_62]: (k3_xboole_0(B_61, A_62)=k3_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.52/9.98  tff(c_42, plain, (![A_25, B_26]: (r1_tarski(k3_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.52/9.98  tff(c_153, plain, (![B_61, A_62]: (r1_tarski(k3_xboole_0(B_61, A_62), A_62))), inference(superposition, [status(thm), theory('equality')], [c_138, c_42])).
% 17.52/9.98  tff(c_2092, plain, (![A_181, B_182, C_183]: (r1_tarski(k3_xboole_0(A_181, k3_xboole_0(B_182, C_183)), C_183))), inference(superposition, [status(thm), theory('equality')], [c_1839, c_153])).
% 17.52/9.98  tff(c_2590, plain, (![A_198, A_199, B_200]: (r1_tarski(k3_xboole_0(A_198, A_199), k2_xboole_0(A_199, B_200)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2092])).
% 17.52/9.98  tff(c_2658, plain, (![B_4, A_3, B_200]: (r1_tarski(k3_xboole_0(B_4, A_3), k2_xboole_0(B_4, B_200)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2590])).
% 17.52/9.98  tff(c_19522, plain, (![B_200]: (r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k2_xboole_0(k1_tarski('#skF_7'), B_200)))), inference(superposition, [status(thm), theory('equality')], [c_19372, c_2658])).
% 17.52/9.98  tff(c_43982, plain, (![A_672, C_673]: (r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k1_enumset1(A_672, '#skF_7', C_673)))), inference(superposition, [status(thm), theory('equality')], [c_26800, c_19522])).
% 17.52/9.98  tff(c_58, plain, (![A_43, B_44, C_45, D_46]: (k1_enumset1(A_43, B_44, C_45)=D_46 | k2_tarski(A_43, C_45)=D_46 | k2_tarski(B_44, C_45)=D_46 | k2_tarski(A_43, B_44)=D_46 | k1_tarski(C_45)=D_46 | k1_tarski(B_44)=D_46 | k1_tarski(A_43)=D_46 | k1_xboole_0=D_46 | ~r1_tarski(D_46, k1_enumset1(A_43, B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.52/9.98  tff(c_43987, plain, (![A_672, C_673]: (k1_enumset1(A_672, '#skF_7', C_673)=k3_xboole_0('#skF_4', '#skF_6') | k3_xboole_0('#skF_4', '#skF_6')=k2_tarski(A_672, C_673) | k3_xboole_0('#skF_4', '#skF_6')=k2_tarski('#skF_7', C_673) | k3_xboole_0('#skF_4', '#skF_6')=k2_tarski(A_672, '#skF_7') | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski(C_673) | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski(A_672) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0)), inference(resolution, [status(thm)], [c_43982, c_58])).
% 17.52/9.98  tff(c_44000, plain, (![A_672, C_673]: (k1_enumset1(A_672, '#skF_7', C_673)=k3_xboole_0('#skF_4', '#skF_6') | k3_xboole_0('#skF_4', '#skF_6')=k2_tarski(A_672, C_673) | k3_xboole_0('#skF_4', '#skF_6')=k2_tarski('#skF_7', C_673) | k3_xboole_0('#skF_4', '#skF_6')=k2_tarski(A_672, '#skF_7') | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski(C_673) | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski(A_672) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_80, c_43987])).
% 17.52/9.98  tff(c_44409, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44000])).
% 17.52/9.98  tff(c_44616, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_44409, c_46])).
% 17.52/9.98  tff(c_44686, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23970, c_44616])).
% 17.52/9.98  tff(c_44688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11090, c_44686])).
% 17.52/9.98  tff(c_44690, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44000])).
% 17.52/9.98  tff(c_52, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.52/9.98  tff(c_27831, plain, (![C_482, A_483, B_484]: (k2_xboole_0(k1_tarski(C_482), k1_enumset1(A_483, B_484, C_482))=k1_enumset1(A_483, B_484, C_482))), inference(resolution, [status(thm)], [c_68, c_258])).
% 17.52/9.98  tff(c_44692, plain, (![A_681, B_682]: (r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k1_enumset1(A_681, B_682, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_27831, c_19522])).
% 17.52/9.98  tff(c_44706, plain, (![A_34]: (r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k2_tarski(A_34, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_44692])).
% 17.52/9.98  tff(c_4996, plain, (![A_284, B_285, C_286, D_287]: (k1_enumset1(A_284, B_285, C_286)=D_287 | k2_tarski(A_284, C_286)=D_287 | k2_tarski(B_285, C_286)=D_287 | k2_tarski(A_284, B_285)=D_287 | k1_tarski(C_286)=D_287 | k1_tarski(B_285)=D_287 | k1_tarski(A_284)=D_287 | k1_xboole_0=D_287 | ~r1_tarski(D_287, k1_enumset1(A_284, B_285, C_286)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.52/9.98  tff(c_5050, plain, (![A_34, B_35, D_287]: (k1_enumset1(A_34, A_34, B_35)=D_287 | k2_tarski(A_34, B_35)=D_287 | k2_tarski(A_34, B_35)=D_287 | k2_tarski(A_34, A_34)=D_287 | k1_tarski(B_35)=D_287 | k1_tarski(A_34)=D_287 | k1_tarski(A_34)=D_287 | k1_xboole_0=D_287 | ~r1_tarski(D_287, k2_tarski(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4996])).
% 17.52/9.98  tff(c_51890, plain, (![A_776, B_777, D_778]: (k2_tarski(A_776, B_777)=D_778 | k2_tarski(A_776, B_777)=D_778 | k2_tarski(A_776, B_777)=D_778 | k1_tarski(A_776)=D_778 | k1_tarski(B_777)=D_778 | k1_tarski(A_776)=D_778 | k1_tarski(A_776)=D_778 | k1_xboole_0=D_778 | ~r1_tarski(D_778, k2_tarski(A_776, B_777)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_5050])).
% 17.52/9.98  tff(c_51904, plain, (![A_34]: (k3_xboole_0('#skF_4', '#skF_6')=k2_tarski(A_34, '#skF_7') | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski(A_34) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0)), inference(resolution, [status(thm)], [c_44706, c_51890])).
% 17.52/9.98  tff(c_52466, plain, (![A_780]: (k3_xboole_0('#skF_4', '#skF_6')=k2_tarski(A_780, '#skF_7') | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski(A_780))), inference(negUnitSimplification, [status(thm)], [c_44690, c_80, c_51904])).
% 17.52/9.98  tff(c_386, plain, (![A_88, B_89]: (k2_xboole_0(k3_xboole_0(A_88, B_89), A_88)=A_88)), inference(resolution, [status(thm)], [c_42, c_258])).
% 17.52/9.98  tff(c_7094, plain, (![A_318, B_319]: (k3_xboole_0(k3_xboole_0(A_318, B_319), A_318)=k3_xboole_0(A_318, B_319))), inference(superposition, [status(thm), theory('equality')], [c_386, c_44])).
% 17.52/9.98  tff(c_7676, plain, (![A_324, B_325]: (k3_xboole_0(k3_xboole_0(A_324, B_325), B_325)=k3_xboole_0(B_325, A_324))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7094])).
% 17.52/9.98  tff(c_7930, plain, (k3_xboole_0('#skF_5', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_338, c_7676])).
% 17.52/9.98  tff(c_8021, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_7930])).
% 17.52/9.98  tff(c_159, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_138, c_84])).
% 17.52/9.98  tff(c_6655, plain, (![A_311, B_312, C_313]: (r1_tarski(k3_xboole_0(A_311, k3_xboole_0(B_312, C_313)), k3_xboole_0(A_311, B_312)))), inference(superposition, [status(thm), theory('equality')], [c_1839, c_42])).
% 17.52/9.98  tff(c_6771, plain, (![C_313]: (r1_tarski(k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_313)), k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_159, c_6655])).
% 17.52/9.98  tff(c_8041, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_4'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8021, c_6771])).
% 17.52/9.98  tff(c_8135, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8041])).
% 17.52/9.98  tff(c_32, plain, (![B_19, A_18]: (B_19=A_18 | ~r1_tarski(B_19, A_18) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.52/9.98  tff(c_8280, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_8135, c_32])).
% 17.52/9.98  tff(c_8286, plain, (~r1_tarski(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_8280])).
% 17.52/9.98  tff(c_52640, plain, (![A_780]: (~r1_tarski(k1_tarski('#skF_7'), k2_tarski(A_780, '#skF_7')) | k3_xboole_0('#skF_4', '#skF_6')=k1_tarski(A_780))), inference(superposition, [status(thm), theory('equality')], [c_52466, c_8286])).
% 17.52/9.98  tff(c_52784, plain, (![A_781]: (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski(A_781))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_52640])).
% 17.52/9.98  tff(c_53071, plain, (![A_781]: (k1_tarski(A_781)!=k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_52784, c_80])).
% 17.52/9.98  tff(c_53912, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_53071])).
% 17.52/9.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.52/9.98  
% 17.52/9.98  Inference rules
% 17.52/9.98  ----------------------
% 17.52/9.98  #Ref     : 1
% 17.52/9.98  #Sup     : 13566
% 17.52/9.98  #Fact    : 16
% 17.52/9.98  #Define  : 0
% 17.52/9.98  #Split   : 15
% 17.52/9.98  #Chain   : 0
% 17.52/9.98  #Close   : 0
% 17.52/9.98  
% 17.52/9.98  Ordering : KBO
% 17.52/9.98  
% 17.52/9.98  Simplification rules
% 17.52/9.98  ----------------------
% 17.52/9.98  #Subsume      : 1832
% 17.52/9.98  #Demod        : 13082
% 17.52/9.98  #Tautology    : 6499
% 17.52/9.98  #SimpNegUnit  : 105
% 17.52/9.98  #BackRed      : 31
% 17.52/9.98  
% 17.52/9.98  #Partial instantiations: 0
% 17.52/9.98  #Strategies tried      : 1
% 17.52/9.98  
% 17.52/9.98  Timing (in seconds)
% 17.52/9.98  ----------------------
% 17.75/9.98  Preprocessing        : 0.34
% 17.75/9.98  Parsing              : 0.18
% 17.75/9.98  CNF conversion       : 0.03
% 17.75/9.98  Main loop            : 8.86
% 17.75/9.98  Inferencing          : 1.13
% 17.75/9.98  Reduction            : 5.46
% 17.75/9.98  Demodulation         : 4.86
% 17.75/9.98  BG Simplification    : 0.13
% 17.75/9.98  Subsumption          : 1.76
% 17.75/9.98  Abstraction          : 0.19
% 17.75/9.98  MUC search           : 0.00
% 17.75/9.98  Cooper               : 0.00
% 17.75/9.98  Total                : 9.25
% 17.75/9.98  Index Insertion      : 0.00
% 17.75/9.98  Index Deletion       : 0.00
% 17.75/9.98  Index Matching       : 0.00
% 17.75/9.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
