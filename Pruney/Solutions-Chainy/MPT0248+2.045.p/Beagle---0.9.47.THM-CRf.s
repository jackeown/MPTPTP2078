%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:10 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 535 expanded)
%              Number of leaves         :   49 ( 196 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 ( 845 expanded)
%              Number of equality atoms :  106 ( 562 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_90,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_100,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_98,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_76,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_128,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_129,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_70,plain,(
    ! [A_69,B_70] :
      ( r1_xboole_0(k1_tarski(A_69),B_70)
      | r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_80,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    ! [A_38,B_39] : r1_tarski(A_38,k2_xboole_0(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_133,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_44])).

tff(c_394,plain,(
    ! [A_117,B_118] :
      ( k3_xboole_0(A_117,B_118) = A_117
      | ~ r1_tarski(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_409,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_133,c_394])).

tff(c_465,plain,(
    ! [A_126,B_127,C_128] :
      ( ~ r1_xboole_0(A_126,B_127)
      | ~ r2_hidden(C_128,k3_xboole_0(A_126,B_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_474,plain,(
    ! [C_128] :
      ( ~ r1_xboole_0('#skF_5',k1_tarski('#skF_4'))
      | ~ r2_hidden(C_128,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_465])).

tff(c_498,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_1711,plain,(
    ! [A_194,B_195] :
      ( r2_hidden('#skF_3'(A_194,B_195),k3_xboole_0(A_194,B_195))
      | r1_xboole_0(A_194,B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1737,plain,
    ( r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_4')),'#skF_5')
    | r1_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_1711])).

tff(c_1750,plain,(
    r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_4')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_1737])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1757,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1750,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_503,plain,(
    ! [A_131,B_132] :
      ( ~ r1_xboole_0(A_131,B_132)
      | v1_xboole_0(k3_xboole_0(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_8,c_465])).

tff(c_1858,plain,(
    ! [A_201,B_202] :
      ( ~ r1_xboole_0(A_201,B_202)
      | v1_xboole_0(k3_xboole_0(B_202,A_201)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_503])).

tff(c_1886,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_1858])).

tff(c_1901,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1757,c_1886])).

tff(c_1908,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_1901])).

tff(c_42,plain,(
    ! [A_37] : k5_xboole_0(A_37,k1_xboole_0) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    ! [A_45] : k5_xboole_0(A_45,A_45) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_538,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k3_xboole_0(A_135,B_136)) = k4_xboole_0(A_135,B_136) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_557,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k5_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_538])).

tff(c_575,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_557])).

tff(c_3818,plain,(
    ! [B_290,A_291] : k5_xboole_0(B_290,k3_xboole_0(A_291,B_290)) = k4_xboole_0(B_290,A_291) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_538])).

tff(c_138,plain,(
    ! [B_83,A_84] : k5_xboole_0(B_83,A_84) = k5_xboole_0(A_84,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [A_84] : k5_xboole_0(k1_xboole_0,A_84) = A_84 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_42])).

tff(c_1062,plain,(
    ! [A_175,B_176,C_177] : k5_xboole_0(k5_xboole_0(A_175,B_176),C_177) = k5_xboole_0(A_175,k5_xboole_0(B_176,C_177)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1126,plain,(
    ! [A_45,C_177] : k5_xboole_0(A_45,k5_xboole_0(A_45,C_177)) = k5_xboole_0(k1_xboole_0,C_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1062])).

tff(c_1139,plain,(
    ! [A_45,C_177] : k5_xboole_0(A_45,k5_xboole_0(A_45,C_177)) = C_177 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1126])).

tff(c_4601,plain,(
    ! [B_305,A_306] : k5_xboole_0(B_305,k4_xboole_0(B_305,A_306)) = k3_xboole_0(A_306,B_305) ),
    inference(superposition,[status(thm),theory(equality)],[c_3818,c_1139])).

tff(c_4658,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_4601])).

tff(c_4677,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4658])).

tff(c_68,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k1_tarski(A_67),B_68)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_408,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(k1_tarski(A_67),B_68) = k1_tarski(A_67)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_68,c_394])).

tff(c_4852,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4677,c_408])).

tff(c_4951,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_4852])).

tff(c_4953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_4951])).

tff(c_4956,plain,(
    ! [C_309] : ~ r2_hidden(C_309,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_4961,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_4956])).

tff(c_24,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4964,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4961,c_24])).

tff(c_4968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_4964])).

tff(c_4969,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_22,plain,(
    ! [A_16] : k3_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7267,plain,(
    ! [A_463,B_464,C_465] : k3_xboole_0(k3_xboole_0(A_463,B_464),C_465) = k3_xboole_0(A_463,k3_xboole_0(B_464,C_465)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9211,plain,(
    ! [A_545,C_546] : k3_xboole_0(A_545,k3_xboole_0(A_545,C_546)) = k3_xboole_0(A_545,C_546) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_7267])).

tff(c_9322,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9211])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4999,plain,(
    ! [B_313,A_314] : k5_xboole_0(B_313,A_314) = k5_xboole_0(A_314,B_313) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5015,plain,(
    ! [A_314] : k5_xboole_0(k1_xboole_0,A_314) = A_314 ),
    inference(superposition,[status(thm),theory(equality)],[c_4999,c_42])).

tff(c_6558,plain,(
    ! [A_434,B_435,C_436] : k5_xboole_0(k5_xboole_0(A_434,B_435),C_436) = k5_xboole_0(A_434,k5_xboole_0(B_435,C_436)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6622,plain,(
    ! [A_45,C_436] : k5_xboole_0(A_45,k5_xboole_0(A_45,C_436)) = k5_xboole_0(k1_xboole_0,C_436) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_6558])).

tff(c_6636,plain,(
    ! [A_437,C_438] : k5_xboole_0(A_437,k5_xboole_0(A_437,C_438)) = C_438 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5015,c_6622])).

tff(c_6679,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6636])).

tff(c_4970,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4978,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4970,c_80])).

tff(c_6484,plain,(
    ! [A_430,B_431] : k4_xboole_0(k2_xboole_0(A_430,B_431),k3_xboole_0(A_430,B_431)) = k5_xboole_0(A_430,B_431) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6520,plain,(
    k4_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_6')) = k5_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4978,c_6484])).

tff(c_6527,plain,(
    k4_xboole_0('#skF_5',k3_xboole_0('#skF_6','#skF_5')) = k5_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_6520])).

tff(c_32,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12689,plain,(
    ! [A_620,B_621] : k5_xboole_0(A_620,k4_xboole_0(A_620,B_621)) = k3_xboole_0(A_620,B_621) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6636])).

tff(c_12743,plain,(
    k5_xboole_0('#skF_5',k5_xboole_0('#skF_6','#skF_5')) = k3_xboole_0('#skF_5',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6527,c_12689])).

tff(c_12773,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9322,c_6679,c_12743])).

tff(c_78,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4998,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4970,c_4970,c_78])).

tff(c_7364,plain,(
    ! [A_16,C_465] : k3_xboole_0(A_16,k3_xboole_0(A_16,C_465)) = k3_xboole_0(A_16,C_465) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_7267])).

tff(c_5469,plain,(
    ! [A_361,B_362] : k5_xboole_0(A_361,k3_xboole_0(A_361,B_362)) = k4_xboole_0(A_361,B_362) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9347,plain,(
    ! [A_547,B_548] : k5_xboole_0(A_547,k3_xboole_0(B_548,A_547)) = k4_xboole_0(A_547,B_548) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5469])).

tff(c_9383,plain,(
    ! [A_16,C_465] : k5_xboole_0(k3_xboole_0(A_16,C_465),k3_xboole_0(A_16,C_465)) = k4_xboole_0(k3_xboole_0(A_16,C_465),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_7364,c_9347])).

tff(c_9436,plain,(
    ! [A_549,C_550] : k4_xboole_0(k3_xboole_0(A_549,C_550),A_549) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9383])).

tff(c_9479,plain,(
    ! [B_2,A_1] : k4_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9436])).

tff(c_12848,plain,(
    k4_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12773,c_9479])).

tff(c_5427,plain,(
    ! [A_354,B_355] :
      ( r1_xboole_0(k1_tarski(A_354),B_355)
      | r2_hidden(A_354,B_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5435,plain,(
    ! [B_356] :
      ( r1_xboole_0('#skF_5',B_356)
      | r2_hidden('#skF_4',B_356) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4970,c_5427])).

tff(c_5130,plain,(
    ! [A_320,B_321] :
      ( r1_tarski(k1_tarski(A_320),B_321)
      | ~ r2_hidden(A_320,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5133,plain,(
    ! [B_321] :
      ( r1_tarski('#skF_5',B_321)
      | ~ r2_hidden('#skF_4',B_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4970,c_5130])).

tff(c_5442,plain,(
    ! [B_356] :
      ( r1_tarski('#skF_5',B_356)
      | r1_xboole_0('#skF_5',B_356) ) ),
    inference(resolution,[status(thm)],[c_5435,c_5133])).

tff(c_5519,plain,(
    ! [A_364,B_365,C_366] :
      ( ~ r1_xboole_0(A_364,B_365)
      | ~ r2_hidden(C_366,k3_xboole_0(A_364,B_365)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5552,plain,(
    ! [A_364,B_365] :
      ( ~ r1_xboole_0(A_364,B_365)
      | v1_xboole_0(k3_xboole_0(A_364,B_365)) ) ),
    inference(resolution,[status(thm)],[c_8,c_5519])).

tff(c_7013,plain,(
    ! [A_447,B_448] :
      ( r2_hidden('#skF_3'(A_447,B_448),k3_xboole_0(A_447,B_448))
      | r1_xboole_0(A_447,B_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7193,plain,(
    ! [A_458,B_459] :
      ( ~ v1_xboole_0(k3_xboole_0(A_458,B_459))
      | r1_xboole_0(A_458,B_459) ) ),
    inference(resolution,[status(thm)],[c_7013,c_6])).

tff(c_7240,plain,(
    ! [A_461,B_462] :
      ( ~ v1_xboole_0(k3_xboole_0(A_461,B_462))
      | r1_xboole_0(B_462,A_461) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7193])).

tff(c_7373,plain,(
    ! [B_466,A_467] :
      ( r1_xboole_0(B_466,A_467)
      | ~ r1_xboole_0(A_467,B_466) ) ),
    inference(resolution,[status(thm)],[c_5552,c_7240])).

tff(c_7391,plain,(
    ! [B_356] :
      ( r1_xboole_0(B_356,'#skF_5')
      | r1_tarski('#skF_5',B_356) ) ),
    inference(resolution,[status(thm)],[c_5442,c_7373])).

tff(c_12890,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12773,c_5552])).

tff(c_13031,plain,(
    ~ r1_xboole_0('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_12890])).

tff(c_13078,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_7391,c_13031])).

tff(c_5803,plain,(
    ! [A_393,B_394] :
      ( r2_xboole_0(A_393,B_394)
      | B_394 = A_393
      | ~ r1_tarski(A_393,B_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [B_29,A_28] :
      ( k4_xboole_0(B_29,A_28) != k1_xboole_0
      | ~ r2_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5814,plain,(
    ! [B_394,A_393] :
      ( k4_xboole_0(B_394,A_393) != k1_xboole_0
      | B_394 = A_393
      | ~ r1_tarski(A_393,B_394) ) ),
    inference(resolution,[status(thm)],[c_5803,c_34])).

tff(c_13089,plain,
    ( k4_xboole_0('#skF_6','#skF_5') != k1_xboole_0
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_13078,c_5814])).

tff(c_13129,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12848,c_13089])).

tff(c_13131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4998,c_13129])).

tff(c_13132,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_12890])).

tff(c_5443,plain,(
    ! [B_356] :
      ( ~ v1_xboole_0(B_356)
      | r1_xboole_0('#skF_5',B_356) ) ),
    inference(resolution,[status(thm)],[c_5435,c_6])).

tff(c_7392,plain,(
    ! [B_356] :
      ( r1_xboole_0(B_356,'#skF_5')
      | ~ v1_xboole_0(B_356) ) ),
    inference(resolution,[status(thm)],[c_5443,c_7373])).

tff(c_7048,plain,(
    ! [A_449,B_450] :
      ( ~ r1_xboole_0(A_449,B_450)
      | v1_xboole_0(k3_xboole_0(A_449,B_450)) ) ),
    inference(resolution,[status(thm)],[c_8,c_5519])).

tff(c_7575,plain,(
    ! [A_475,B_476] :
      ( k3_xboole_0(A_475,B_476) = k1_xboole_0
      | ~ r1_xboole_0(A_475,B_476) ) ),
    inference(resolution,[status(thm)],[c_7048,c_24])).

tff(c_7607,plain,(
    ! [B_356] :
      ( k3_xboole_0(B_356,'#skF_5') = k1_xboole_0
      | ~ v1_xboole_0(B_356) ) ),
    inference(resolution,[status(thm)],[c_7392,c_7575])).

tff(c_13136,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13132,c_7607])).

tff(c_13154,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12773,c_13136])).

tff(c_13156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4969,c_13154])).

tff(c_13157,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),A_9)
      | r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_13179,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_44])).

tff(c_13419,plain,(
    ! [A_654,B_655] :
      ( k3_xboole_0(A_654,B_655) = A_654
      | ~ r1_tarski(A_654,B_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13434,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_13179,c_13419])).

tff(c_13541,plain,(
    ! [A_674,B_675,C_676] :
      ( ~ r1_xboole_0(A_674,B_675)
      | ~ r2_hidden(C_676,k3_xboole_0(A_674,B_675)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_13554,plain,(
    ! [C_676] :
      ( ~ r1_xboole_0('#skF_5',k1_tarski('#skF_4'))
      | ~ r2_hidden(C_676,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13434,c_13541])).

tff(c_13662,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13554])).

tff(c_13666,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_13662])).

tff(c_13158,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_13160,plain,(
    ! [A_37] : k5_xboole_0(A_37,'#skF_5') = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13158,c_42])).

tff(c_13707,plain,(
    ! [A_695,B_696] : k5_xboole_0(A_695,k3_xboole_0(A_695,B_696)) = k4_xboole_0(A_695,B_696) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_13723,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k5_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13434,c_13707])).

tff(c_13740,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13160,c_13723])).

tff(c_13742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13666,c_13740])).

tff(c_13745,plain,(
    ! [C_697] : ~ r2_hidden(C_697,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_13554])).

tff(c_13768,plain,(
    ! [B_698] : r1_tarski('#skF_5',B_698) ),
    inference(resolution,[status(thm)],[c_14,c_13745])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_13776,plain,(
    ! [B_698] : k2_xboole_0('#skF_5',B_698) = B_698 ),
    inference(resolution,[status(thm)],[c_13768,c_36])).

tff(c_13782,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13776,c_80])).

tff(c_13784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13157,c_13782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.50/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.72  
% 7.84/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.72  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 7.84/2.72  
% 7.84/2.72  %Foreground sorts:
% 7.84/2.72  
% 7.84/2.72  
% 7.84/2.72  %Background operators:
% 7.84/2.72  
% 7.84/2.72  
% 7.84/2.72  %Foreground operators:
% 7.84/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.84/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.84/2.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.84/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.84/2.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.84/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.84/2.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.84/2.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.84/2.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.84/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.84/2.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.84/2.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.84/2.72  tff('#skF_5', type, '#skF_5': $i).
% 7.84/2.72  tff('#skF_6', type, '#skF_6': $i).
% 7.84/2.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.84/2.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.84/2.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.84/2.72  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 7.84/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.84/2.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.84/2.72  tff('#skF_4', type, '#skF_4': $i).
% 7.84/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.84/2.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.84/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.84/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.84/2.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.84/2.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.84/2.72  
% 7.84/2.75  tff(f_142, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 7.84/2.75  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.84/2.75  tff(f_121, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.84/2.75  tff(f_92, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.84/2.75  tff(f_88, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.84/2.75  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.84/2.75  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.84/2.75  tff(f_90, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.84/2.75  tff(f_100, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.84/2.75  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.84/2.75  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.84/2.75  tff(f_98, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.84/2.75  tff(f_116, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.84/2.75  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.84/2.75  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.84/2.75  tff(f_84, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.84/2.75  tff(f_71, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 7.84/2.75  tff(f_49, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 7.84/2.75  tff(f_78, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 7.84/2.75  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.84/2.75  tff(f_96, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.84/2.75  tff(f_82, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.84/2.75  tff(c_76, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.84/2.75  tff(c_128, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_76])).
% 7.84/2.75  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.84/2.75  tff(c_74, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.84/2.75  tff(c_129, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_74])).
% 7.84/2.75  tff(c_70, plain, (![A_69, B_70]: (r1_xboole_0(k1_tarski(A_69), B_70) | r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.84/2.75  tff(c_80, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.84/2.75  tff(c_44, plain, (![A_38, B_39]: (r1_tarski(A_38, k2_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.84/2.75  tff(c_133, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_44])).
% 7.84/2.75  tff(c_394, plain, (![A_117, B_118]: (k3_xboole_0(A_117, B_118)=A_117 | ~r1_tarski(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.84/2.75  tff(c_409, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_133, c_394])).
% 7.84/2.75  tff(c_465, plain, (![A_126, B_127, C_128]: (~r1_xboole_0(A_126, B_127) | ~r2_hidden(C_128, k3_xboole_0(A_126, B_127)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.84/2.75  tff(c_474, plain, (![C_128]: (~r1_xboole_0('#skF_5', k1_tarski('#skF_4')) | ~r2_hidden(C_128, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_465])).
% 7.84/2.75  tff(c_498, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_474])).
% 7.84/2.75  tff(c_1711, plain, (![A_194, B_195]: (r2_hidden('#skF_3'(A_194, B_195), k3_xboole_0(A_194, B_195)) | r1_xboole_0(A_194, B_195))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.84/2.75  tff(c_1737, plain, (r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_4')), '#skF_5') | r1_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_1711])).
% 7.84/2.75  tff(c_1750, plain, (r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_4')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_498, c_1737])).
% 7.84/2.75  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.84/2.75  tff(c_1757, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1750, c_6])).
% 7.84/2.75  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.84/2.75  tff(c_503, plain, (![A_131, B_132]: (~r1_xboole_0(A_131, B_132) | v1_xboole_0(k3_xboole_0(A_131, B_132)))), inference(resolution, [status(thm)], [c_8, c_465])).
% 7.84/2.75  tff(c_1858, plain, (![A_201, B_202]: (~r1_xboole_0(A_201, B_202) | v1_xboole_0(k3_xboole_0(B_202, A_201)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_503])).
% 7.84/2.75  tff(c_1886, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_409, c_1858])).
% 7.84/2.75  tff(c_1901, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1757, c_1886])).
% 7.84/2.75  tff(c_1908, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_1901])).
% 7.84/2.75  tff(c_42, plain, (![A_37]: (k5_xboole_0(A_37, k1_xboole_0)=A_37)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.84/2.75  tff(c_52, plain, (![A_45]: (k5_xboole_0(A_45, A_45)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.84/2.75  tff(c_538, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k3_xboole_0(A_135, B_136))=k4_xboole_0(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.84/2.75  tff(c_557, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k5_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_409, c_538])).
% 7.84/2.75  tff(c_575, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_557])).
% 7.84/2.75  tff(c_3818, plain, (![B_290, A_291]: (k5_xboole_0(B_290, k3_xboole_0(A_291, B_290))=k4_xboole_0(B_290, A_291))), inference(superposition, [status(thm), theory('equality')], [c_2, c_538])).
% 7.84/2.75  tff(c_138, plain, (![B_83, A_84]: (k5_xboole_0(B_83, A_84)=k5_xboole_0(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.84/2.75  tff(c_154, plain, (![A_84]: (k5_xboole_0(k1_xboole_0, A_84)=A_84)), inference(superposition, [status(thm), theory('equality')], [c_138, c_42])).
% 7.84/2.75  tff(c_1062, plain, (![A_175, B_176, C_177]: (k5_xboole_0(k5_xboole_0(A_175, B_176), C_177)=k5_xboole_0(A_175, k5_xboole_0(B_176, C_177)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.84/2.75  tff(c_1126, plain, (![A_45, C_177]: (k5_xboole_0(A_45, k5_xboole_0(A_45, C_177))=k5_xboole_0(k1_xboole_0, C_177))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1062])).
% 7.84/2.75  tff(c_1139, plain, (![A_45, C_177]: (k5_xboole_0(A_45, k5_xboole_0(A_45, C_177))=C_177)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1126])).
% 7.84/2.75  tff(c_4601, plain, (![B_305, A_306]: (k5_xboole_0(B_305, k4_xboole_0(B_305, A_306))=k3_xboole_0(A_306, B_305))), inference(superposition, [status(thm), theory('equality')], [c_3818, c_1139])).
% 7.84/2.75  tff(c_4658, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_575, c_4601])).
% 7.84/2.75  tff(c_4677, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4658])).
% 7.84/2.75  tff(c_68, plain, (![A_67, B_68]: (r1_tarski(k1_tarski(A_67), B_68) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.84/2.75  tff(c_408, plain, (![A_67, B_68]: (k3_xboole_0(k1_tarski(A_67), B_68)=k1_tarski(A_67) | ~r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_68, c_394])).
% 7.84/2.75  tff(c_4852, plain, (k1_tarski('#skF_4')='#skF_5' | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4677, c_408])).
% 7.84/2.75  tff(c_4951, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_4852])).
% 7.84/2.75  tff(c_4953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_4951])).
% 7.84/2.75  tff(c_4956, plain, (![C_309]: (~r2_hidden(C_309, '#skF_5'))), inference(splitRight, [status(thm)], [c_474])).
% 7.84/2.75  tff(c_4961, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_8, c_4956])).
% 7.84/2.75  tff(c_24, plain, (![A_18]: (k1_xboole_0=A_18 | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.84/2.75  tff(c_4964, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4961, c_24])).
% 7.84/2.75  tff(c_4968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_4964])).
% 7.84/2.75  tff(c_4969, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 7.84/2.75  tff(c_22, plain, (![A_16]: (k3_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.84/2.75  tff(c_7267, plain, (![A_463, B_464, C_465]: (k3_xboole_0(k3_xboole_0(A_463, B_464), C_465)=k3_xboole_0(A_463, k3_xboole_0(B_464, C_465)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.84/2.75  tff(c_9211, plain, (![A_545, C_546]: (k3_xboole_0(A_545, k3_xboole_0(A_545, C_546))=k3_xboole_0(A_545, C_546))), inference(superposition, [status(thm), theory('equality')], [c_22, c_7267])).
% 7.84/2.75  tff(c_9322, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9211])).
% 7.84/2.75  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.84/2.75  tff(c_4999, plain, (![B_313, A_314]: (k5_xboole_0(B_313, A_314)=k5_xboole_0(A_314, B_313))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.84/2.75  tff(c_5015, plain, (![A_314]: (k5_xboole_0(k1_xboole_0, A_314)=A_314)), inference(superposition, [status(thm), theory('equality')], [c_4999, c_42])).
% 7.84/2.75  tff(c_6558, plain, (![A_434, B_435, C_436]: (k5_xboole_0(k5_xboole_0(A_434, B_435), C_436)=k5_xboole_0(A_434, k5_xboole_0(B_435, C_436)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.84/2.75  tff(c_6622, plain, (![A_45, C_436]: (k5_xboole_0(A_45, k5_xboole_0(A_45, C_436))=k5_xboole_0(k1_xboole_0, C_436))), inference(superposition, [status(thm), theory('equality')], [c_52, c_6558])).
% 7.84/2.75  tff(c_6636, plain, (![A_437, C_438]: (k5_xboole_0(A_437, k5_xboole_0(A_437, C_438))=C_438)), inference(demodulation, [status(thm), theory('equality')], [c_5015, c_6622])).
% 7.84/2.75  tff(c_6679, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_6636])).
% 7.84/2.75  tff(c_4970, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_74])).
% 7.84/2.75  tff(c_4978, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4970, c_80])).
% 7.84/2.75  tff(c_6484, plain, (![A_430, B_431]: (k4_xboole_0(k2_xboole_0(A_430, B_431), k3_xboole_0(A_430, B_431))=k5_xboole_0(A_430, B_431))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.84/2.75  tff(c_6520, plain, (k4_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4978, c_6484])).
% 7.84/2.75  tff(c_6527, plain, (k4_xboole_0('#skF_5', k3_xboole_0('#skF_6', '#skF_5'))=k5_xboole_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_6520])).
% 7.84/2.75  tff(c_32, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.84/2.75  tff(c_12689, plain, (![A_620, B_621]: (k5_xboole_0(A_620, k4_xboole_0(A_620, B_621))=k3_xboole_0(A_620, B_621))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6636])).
% 7.84/2.75  tff(c_12743, plain, (k5_xboole_0('#skF_5', k5_xboole_0('#skF_6', '#skF_5'))=k3_xboole_0('#skF_5', k3_xboole_0('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6527, c_12689])).
% 7.84/2.75  tff(c_12773, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9322, c_6679, c_12743])).
% 7.84/2.75  tff(c_78, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.84/2.75  tff(c_4998, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4970, c_4970, c_78])).
% 7.84/2.75  tff(c_7364, plain, (![A_16, C_465]: (k3_xboole_0(A_16, k3_xboole_0(A_16, C_465))=k3_xboole_0(A_16, C_465))), inference(superposition, [status(thm), theory('equality')], [c_22, c_7267])).
% 7.84/2.75  tff(c_5469, plain, (![A_361, B_362]: (k5_xboole_0(A_361, k3_xboole_0(A_361, B_362))=k4_xboole_0(A_361, B_362))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.84/2.75  tff(c_9347, plain, (![A_547, B_548]: (k5_xboole_0(A_547, k3_xboole_0(B_548, A_547))=k4_xboole_0(A_547, B_548))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5469])).
% 7.84/2.75  tff(c_9383, plain, (![A_16, C_465]: (k5_xboole_0(k3_xboole_0(A_16, C_465), k3_xboole_0(A_16, C_465))=k4_xboole_0(k3_xboole_0(A_16, C_465), A_16))), inference(superposition, [status(thm), theory('equality')], [c_7364, c_9347])).
% 7.84/2.75  tff(c_9436, plain, (![A_549, C_550]: (k4_xboole_0(k3_xboole_0(A_549, C_550), A_549)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_9383])).
% 7.84/2.75  tff(c_9479, plain, (![B_2, A_1]: (k4_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_9436])).
% 7.84/2.75  tff(c_12848, plain, (k4_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12773, c_9479])).
% 7.84/2.75  tff(c_5427, plain, (![A_354, B_355]: (r1_xboole_0(k1_tarski(A_354), B_355) | r2_hidden(A_354, B_355))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.84/2.75  tff(c_5435, plain, (![B_356]: (r1_xboole_0('#skF_5', B_356) | r2_hidden('#skF_4', B_356))), inference(superposition, [status(thm), theory('equality')], [c_4970, c_5427])).
% 7.84/2.75  tff(c_5130, plain, (![A_320, B_321]: (r1_tarski(k1_tarski(A_320), B_321) | ~r2_hidden(A_320, B_321))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.84/2.75  tff(c_5133, plain, (![B_321]: (r1_tarski('#skF_5', B_321) | ~r2_hidden('#skF_4', B_321))), inference(superposition, [status(thm), theory('equality')], [c_4970, c_5130])).
% 7.84/2.75  tff(c_5442, plain, (![B_356]: (r1_tarski('#skF_5', B_356) | r1_xboole_0('#skF_5', B_356))), inference(resolution, [status(thm)], [c_5435, c_5133])).
% 7.84/2.75  tff(c_5519, plain, (![A_364, B_365, C_366]: (~r1_xboole_0(A_364, B_365) | ~r2_hidden(C_366, k3_xboole_0(A_364, B_365)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.84/2.75  tff(c_5552, plain, (![A_364, B_365]: (~r1_xboole_0(A_364, B_365) | v1_xboole_0(k3_xboole_0(A_364, B_365)))), inference(resolution, [status(thm)], [c_8, c_5519])).
% 7.84/2.75  tff(c_7013, plain, (![A_447, B_448]: (r2_hidden('#skF_3'(A_447, B_448), k3_xboole_0(A_447, B_448)) | r1_xboole_0(A_447, B_448))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.84/2.75  tff(c_7193, plain, (![A_458, B_459]: (~v1_xboole_0(k3_xboole_0(A_458, B_459)) | r1_xboole_0(A_458, B_459))), inference(resolution, [status(thm)], [c_7013, c_6])).
% 7.84/2.75  tff(c_7240, plain, (![A_461, B_462]: (~v1_xboole_0(k3_xboole_0(A_461, B_462)) | r1_xboole_0(B_462, A_461))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7193])).
% 7.84/2.75  tff(c_7373, plain, (![B_466, A_467]: (r1_xboole_0(B_466, A_467) | ~r1_xboole_0(A_467, B_466))), inference(resolution, [status(thm)], [c_5552, c_7240])).
% 7.84/2.75  tff(c_7391, plain, (![B_356]: (r1_xboole_0(B_356, '#skF_5') | r1_tarski('#skF_5', B_356))), inference(resolution, [status(thm)], [c_5442, c_7373])).
% 7.84/2.75  tff(c_12890, plain, (~r1_xboole_0('#skF_6', '#skF_5') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12773, c_5552])).
% 7.84/2.75  tff(c_13031, plain, (~r1_xboole_0('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_12890])).
% 7.84/2.75  tff(c_13078, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_7391, c_13031])).
% 7.84/2.75  tff(c_5803, plain, (![A_393, B_394]: (r2_xboole_0(A_393, B_394) | B_394=A_393 | ~r1_tarski(A_393, B_394))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.84/2.75  tff(c_34, plain, (![B_29, A_28]: (k4_xboole_0(B_29, A_28)!=k1_xboole_0 | ~r2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.84/2.75  tff(c_5814, plain, (![B_394, A_393]: (k4_xboole_0(B_394, A_393)!=k1_xboole_0 | B_394=A_393 | ~r1_tarski(A_393, B_394))), inference(resolution, [status(thm)], [c_5803, c_34])).
% 7.84/2.75  tff(c_13089, plain, (k4_xboole_0('#skF_6', '#skF_5')!=k1_xboole_0 | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_13078, c_5814])).
% 7.84/2.75  tff(c_13129, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12848, c_13089])).
% 7.84/2.75  tff(c_13131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4998, c_13129])).
% 7.84/2.75  tff(c_13132, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_12890])).
% 7.84/2.75  tff(c_5443, plain, (![B_356]: (~v1_xboole_0(B_356) | r1_xboole_0('#skF_5', B_356))), inference(resolution, [status(thm)], [c_5435, c_6])).
% 7.84/2.75  tff(c_7392, plain, (![B_356]: (r1_xboole_0(B_356, '#skF_5') | ~v1_xboole_0(B_356))), inference(resolution, [status(thm)], [c_5443, c_7373])).
% 7.84/2.75  tff(c_7048, plain, (![A_449, B_450]: (~r1_xboole_0(A_449, B_450) | v1_xboole_0(k3_xboole_0(A_449, B_450)))), inference(resolution, [status(thm)], [c_8, c_5519])).
% 7.84/2.75  tff(c_7575, plain, (![A_475, B_476]: (k3_xboole_0(A_475, B_476)=k1_xboole_0 | ~r1_xboole_0(A_475, B_476))), inference(resolution, [status(thm)], [c_7048, c_24])).
% 7.84/2.75  tff(c_7607, plain, (![B_356]: (k3_xboole_0(B_356, '#skF_5')=k1_xboole_0 | ~v1_xboole_0(B_356))), inference(resolution, [status(thm)], [c_7392, c_7575])).
% 7.84/2.75  tff(c_13136, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_13132, c_7607])).
% 7.84/2.75  tff(c_13154, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12773, c_13136])).
% 7.84/2.75  tff(c_13156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4969, c_13154])).
% 7.84/2.75  tff(c_13157, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_76])).
% 7.84/2.75  tff(c_14, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), A_9) | r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.84/2.75  tff(c_48, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k4_xboole_0(A_40, B_41)!=A_40)), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.84/2.75  tff(c_13179, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_44])).
% 7.84/2.75  tff(c_13419, plain, (![A_654, B_655]: (k3_xboole_0(A_654, B_655)=A_654 | ~r1_tarski(A_654, B_655))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.84/2.75  tff(c_13434, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_13179, c_13419])).
% 7.84/2.75  tff(c_13541, plain, (![A_674, B_675, C_676]: (~r1_xboole_0(A_674, B_675) | ~r2_hidden(C_676, k3_xboole_0(A_674, B_675)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.84/2.75  tff(c_13554, plain, (![C_676]: (~r1_xboole_0('#skF_5', k1_tarski('#skF_4')) | ~r2_hidden(C_676, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_13434, c_13541])).
% 7.84/2.75  tff(c_13662, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_13554])).
% 7.84/2.75  tff(c_13666, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(resolution, [status(thm)], [c_48, c_13662])).
% 7.84/2.75  tff(c_13158, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_76])).
% 7.84/2.75  tff(c_13160, plain, (![A_37]: (k5_xboole_0(A_37, '#skF_5')=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_13158, c_42])).
% 7.84/2.75  tff(c_13707, plain, (![A_695, B_696]: (k5_xboole_0(A_695, k3_xboole_0(A_695, B_696))=k4_xboole_0(A_695, B_696))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.84/2.75  tff(c_13723, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k5_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13434, c_13707])).
% 7.84/2.75  tff(c_13740, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13160, c_13723])).
% 7.84/2.75  tff(c_13742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13666, c_13740])).
% 7.84/2.75  tff(c_13745, plain, (![C_697]: (~r2_hidden(C_697, '#skF_5'))), inference(splitRight, [status(thm)], [c_13554])).
% 7.84/2.75  tff(c_13768, plain, (![B_698]: (r1_tarski('#skF_5', B_698))), inference(resolution, [status(thm)], [c_14, c_13745])).
% 7.84/2.75  tff(c_36, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.84/2.75  tff(c_13776, plain, (![B_698]: (k2_xboole_0('#skF_5', B_698)=B_698)), inference(resolution, [status(thm)], [c_13768, c_36])).
% 7.84/2.75  tff(c_13782, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_13776, c_80])).
% 7.84/2.75  tff(c_13784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13157, c_13782])).
% 7.84/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.75  
% 7.84/2.75  Inference rules
% 7.84/2.75  ----------------------
% 7.84/2.75  #Ref     : 2
% 7.84/2.75  #Sup     : 3256
% 7.84/2.75  #Fact    : 0
% 7.84/2.75  #Define  : 0
% 7.84/2.75  #Split   : 8
% 7.84/2.75  #Chain   : 0
% 7.84/2.75  #Close   : 0
% 7.84/2.75  
% 7.84/2.75  Ordering : KBO
% 7.84/2.75  
% 7.84/2.75  Simplification rules
% 7.84/2.75  ----------------------
% 7.84/2.75  #Subsume      : 1068
% 7.84/2.75  #Demod        : 1181
% 7.84/2.75  #Tautology    : 1082
% 7.84/2.75  #SimpNegUnit  : 190
% 7.84/2.75  #BackRed      : 32
% 7.84/2.75  
% 7.84/2.75  #Partial instantiations: 0
% 7.84/2.75  #Strategies tried      : 1
% 7.84/2.75  
% 7.84/2.75  Timing (in seconds)
% 7.84/2.75  ----------------------
% 7.84/2.75  Preprocessing        : 0.36
% 7.84/2.75  Parsing              : 0.19
% 7.84/2.75  CNF conversion       : 0.03
% 7.84/2.75  Main loop            : 1.62
% 7.84/2.75  Inferencing          : 0.51
% 7.84/2.75  Reduction            : 0.62
% 7.84/2.75  Demodulation         : 0.46
% 7.84/2.75  BG Simplification    : 0.05
% 7.84/2.75  Subsumption          : 0.32
% 7.84/2.75  Abstraction          : 0.06
% 7.84/2.75  MUC search           : 0.00
% 7.84/2.75  Cooper               : 0.00
% 7.84/2.75  Total                : 2.03
% 7.84/2.75  Index Insertion      : 0.00
% 7.84/2.75  Index Deletion       : 0.00
% 7.84/2.75  Index Matching       : 0.00
% 7.84/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
