%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:13 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 375 expanded)
%              Number of leaves         :   28 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :  183 ( 929 expanded)
%              Number of equality atoms :   16 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_88,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_92,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_97,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [B_37,A_36] :
      ( r1_ordinal1(B_37,A_36)
      | r1_ordinal1(A_36,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_837,plain,(
    ! [A_161,B_162] :
      ( r1_tarski(A_161,B_162)
      | ~ r1_ordinal1(A_161,B_162)
      | ~ v3_ordinal1(B_162)
      | ~ v3_ordinal1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    ! [B_46,A_44] :
      ( r2_hidden(B_46,A_44)
      | r1_ordinal1(A_44,B_46)
      | ~ v3_ordinal1(B_46)
      | ~ v3_ordinal1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ! [A_47] :
      ( v3_ordinal1(k1_ordinal1(A_47))
      | ~ v3_ordinal1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_127,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_58])).

tff(c_273,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(A_92,B_93)
      | ~ r1_ordinal1(A_92,B_93)
      | ~ v3_ordinal1(B_93)
      | ~ v3_ordinal1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_128,plain,(
    ! [A_64,B_65] :
      ( ~ r2_hidden(A_64,B_65)
      | r2_hidden(A_64,k1_ordinal1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [B_49,A_48] :
      ( ~ r1_tarski(B_49,A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_132,plain,(
    ! [B_65,A_64] :
      ( ~ r1_tarski(k1_ordinal1(B_65),A_64)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_128,c_46])).

tff(c_356,plain,(
    ! [B_109,B_110] :
      ( ~ r2_hidden(B_109,B_110)
      | ~ r1_ordinal1(k1_ordinal1(B_110),B_109)
      | ~ v3_ordinal1(B_109)
      | ~ v3_ordinal1(k1_ordinal1(B_110)) ) ),
    inference(resolution,[status(thm)],[c_273,c_132])).

tff(c_379,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_127,c_356])).

tff(c_387,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_379])).

tff(c_388,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_391,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_388])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_391])).

tff(c_396,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_409,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_396])).

tff(c_412,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_409])).

tff(c_211,plain,(
    ! [B_87,A_88] :
      ( r2_hidden(B_87,A_88)
      | r1_ordinal1(A_88,B_87)
      | ~ v3_ordinal1(B_87)
      | ~ v3_ordinal1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_242,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_211,c_88])).

tff(c_255,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_242])).

tff(c_32,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ r1_ordinal1(A_39,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_346,plain,(
    ! [B_107,A_108] :
      ( B_107 = A_108
      | ~ r1_tarski(B_107,A_108)
      | ~ r1_ordinal1(A_108,B_107)
      | ~ v3_ordinal1(B_107)
      | ~ v3_ordinal1(A_108) ) ),
    inference(resolution,[status(thm)],[c_273,c_2])).

tff(c_413,plain,(
    ! [B_117,A_118] :
      ( B_117 = A_118
      | ~ r1_ordinal1(B_117,A_118)
      | ~ r1_ordinal1(A_118,B_117)
      | ~ v3_ordinal1(B_117)
      | ~ v3_ordinal1(A_118) ) ),
    inference(resolution,[status(thm)],[c_32,c_346])).

tff(c_425,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_255,c_413])).

tff(c_439,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_412,c_425])).

tff(c_397,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_133,plain,(
    ! [B_66,A_67] :
      ( ~ r1_tarski(k1_ordinal1(B_66),A_67)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(resolution,[status(thm)],[c_128,c_46])).

tff(c_138,plain,(
    ! [B_66] : ~ r2_hidden(k1_ordinal1(B_66),B_66) ),
    inference(resolution,[status(thm)],[c_6,c_133])).

tff(c_252,plain,(
    ! [A_88] :
      ( r1_ordinal1(A_88,k1_ordinal1(A_88))
      | ~ v3_ordinal1(k1_ordinal1(A_88))
      | ~ v3_ordinal1(A_88) ) ),
    inference(resolution,[status(thm)],[c_211,c_138])).

tff(c_429,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_127,c_413])).

tff(c_444,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_397,c_429])).

tff(c_445,plain,(
    ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_480,plain,(
    ~ r1_ordinal1('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_445])).

tff(c_485,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_252,c_480])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_397,c_485])).

tff(c_490,plain,(
    k1_ordinal1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_510,plain,(
    k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_490])).

tff(c_38,plain,(
    ! [B_43] : r2_hidden(B_43,k1_ordinal1(B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    ! [B_56,A_57] :
      ( ~ r1_tarski(B_56,A_57)
      | ~ r2_hidden(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_86,plain,(
    ! [B_43] : ~ r1_tarski(k1_ordinal1(B_43),B_43) ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_561,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_86])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_561])).

tff(c_589,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_593,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_589,c_46])).

tff(c_851,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_837,c_593])).

tff(c_862,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_851])).

tff(c_866,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_862])).

tff(c_872,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_866])).

tff(c_725,plain,(
    ! [B_151,A_152] :
      ( r1_ordinal1(B_151,A_152)
      | r1_ordinal1(A_152,B_151)
      | ~ v3_ordinal1(B_151)
      | ~ v3_ordinal1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_588,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_728,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_725,c_588])).

tff(c_734,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_728])).

tff(c_739,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_734])).

tff(c_782,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_739])).

tff(c_786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_782])).

tff(c_788,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_734])).

tff(c_796,plain,(
    ! [B_158,A_159] :
      ( r2_hidden(B_158,A_159)
      | r1_ordinal1(A_159,B_158)
      | ~ v3_ordinal1(B_158)
      | ~ v3_ordinal1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [B_43,A_42] :
      ( B_43 = A_42
      | r2_hidden(A_42,B_43)
      | ~ r2_hidden(A_42,k1_ordinal1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1062,plain,(
    ! [B_204,B_203] :
      ( B_204 = B_203
      | r2_hidden(B_204,B_203)
      | r1_ordinal1(k1_ordinal1(B_203),B_204)
      | ~ v3_ordinal1(B_204)
      | ~ v3_ordinal1(k1_ordinal1(B_203)) ) ),
    inference(resolution,[status(thm)],[c_796,c_36])).

tff(c_1074,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1062,c_588])).

tff(c_1081,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_48,c_1074])).

tff(c_1082,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1081])).

tff(c_1086,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1082,c_46])).

tff(c_1089,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1086])).

tff(c_1093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_872,c_1089])).

tff(c_1094,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_1100,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_593])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.52  
% 3.00/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.52  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 3.26/1.52  
% 3.26/1.52  %Foreground sorts:
% 3.26/1.52  
% 3.26/1.52  
% 3.26/1.52  %Background operators:
% 3.26/1.52  
% 3.26/1.52  
% 3.26/1.52  %Foreground operators:
% 3.26/1.52  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.52  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.26/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.52  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.26/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  
% 3.26/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.54  tff(f_107, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.26/1.54  tff(f_61, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 3.26/1.54  tff(f_71, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.26/1.54  tff(f_88, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.26/1.54  tff(f_92, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 3.26/1.54  tff(f_79, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.26/1.54  tff(f_97, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.26/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.54  tff(c_50, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.26/1.54  tff(c_48, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.26/1.54  tff(c_26, plain, (![B_37, A_36]: (r1_ordinal1(B_37, A_36) | r1_ordinal1(A_36, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.54  tff(c_837, plain, (![A_161, B_162]: (r1_tarski(A_161, B_162) | ~r1_ordinal1(A_161, B_162) | ~v3_ordinal1(B_162) | ~v3_ordinal1(A_161))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.26/1.54  tff(c_42, plain, (![B_46, A_44]: (r2_hidden(B_46, A_44) | r1_ordinal1(A_44, B_46) | ~v3_ordinal1(B_46) | ~v3_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.26/1.54  tff(c_44, plain, (![A_47]: (v3_ordinal1(k1_ordinal1(A_47)) | ~v3_ordinal1(A_47))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.26/1.54  tff(c_52, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.26/1.54  tff(c_88, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 3.26/1.54  tff(c_58, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.26/1.54  tff(c_127, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_88, c_58])).
% 3.26/1.54  tff(c_273, plain, (![A_92, B_93]: (r1_tarski(A_92, B_93) | ~r1_ordinal1(A_92, B_93) | ~v3_ordinal1(B_93) | ~v3_ordinal1(A_92))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.26/1.54  tff(c_128, plain, (![A_64, B_65]: (~r2_hidden(A_64, B_65) | r2_hidden(A_64, k1_ordinal1(B_65)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.54  tff(c_46, plain, (![B_49, A_48]: (~r1_tarski(B_49, A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.26/1.54  tff(c_132, plain, (![B_65, A_64]: (~r1_tarski(k1_ordinal1(B_65), A_64) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_128, c_46])).
% 3.26/1.54  tff(c_356, plain, (![B_109, B_110]: (~r2_hidden(B_109, B_110) | ~r1_ordinal1(k1_ordinal1(B_110), B_109) | ~v3_ordinal1(B_109) | ~v3_ordinal1(k1_ordinal1(B_110)))), inference(resolution, [status(thm)], [c_273, c_132])).
% 3.26/1.54  tff(c_379, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_127, c_356])).
% 3.26/1.54  tff(c_387, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_379])).
% 3.26/1.54  tff(c_388, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_387])).
% 3.26/1.54  tff(c_391, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_388])).
% 3.26/1.54  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_391])).
% 3.26/1.54  tff(c_396, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_387])).
% 3.26/1.54  tff(c_409, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_42, c_396])).
% 3.26/1.54  tff(c_412, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_409])).
% 3.26/1.54  tff(c_211, plain, (![B_87, A_88]: (r2_hidden(B_87, A_88) | r1_ordinal1(A_88, B_87) | ~v3_ordinal1(B_87) | ~v3_ordinal1(A_88))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.26/1.54  tff(c_242, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_211, c_88])).
% 3.26/1.54  tff(c_255, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_242])).
% 3.26/1.54  tff(c_32, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~r1_ordinal1(A_39, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.26/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.54  tff(c_346, plain, (![B_107, A_108]: (B_107=A_108 | ~r1_tarski(B_107, A_108) | ~r1_ordinal1(A_108, B_107) | ~v3_ordinal1(B_107) | ~v3_ordinal1(A_108))), inference(resolution, [status(thm)], [c_273, c_2])).
% 3.26/1.54  tff(c_413, plain, (![B_117, A_118]: (B_117=A_118 | ~r1_ordinal1(B_117, A_118) | ~r1_ordinal1(A_118, B_117) | ~v3_ordinal1(B_117) | ~v3_ordinal1(A_118))), inference(resolution, [status(thm)], [c_32, c_346])).
% 3.26/1.54  tff(c_425, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_255, c_413])).
% 3.26/1.54  tff(c_439, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_412, c_425])).
% 3.26/1.54  tff(c_397, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_387])).
% 3.26/1.54  tff(c_133, plain, (![B_66, A_67]: (~r1_tarski(k1_ordinal1(B_66), A_67) | ~r2_hidden(A_67, B_66))), inference(resolution, [status(thm)], [c_128, c_46])).
% 3.26/1.54  tff(c_138, plain, (![B_66]: (~r2_hidden(k1_ordinal1(B_66), B_66))), inference(resolution, [status(thm)], [c_6, c_133])).
% 3.26/1.54  tff(c_252, plain, (![A_88]: (r1_ordinal1(A_88, k1_ordinal1(A_88)) | ~v3_ordinal1(k1_ordinal1(A_88)) | ~v3_ordinal1(A_88))), inference(resolution, [status(thm)], [c_211, c_138])).
% 3.26/1.54  tff(c_429, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_127, c_413])).
% 3.26/1.54  tff(c_444, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_397, c_429])).
% 3.26/1.54  tff(c_445, plain, (~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_444])).
% 3.26/1.54  tff(c_480, plain, (~r1_ordinal1('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_445])).
% 3.26/1.54  tff(c_485, plain, (~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_252, c_480])).
% 3.26/1.54  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_397, c_485])).
% 3.26/1.54  tff(c_490, plain, (k1_ordinal1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_444])).
% 3.26/1.54  tff(c_510, plain, (k1_ordinal1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_490])).
% 3.26/1.54  tff(c_38, plain, (![B_43]: (r2_hidden(B_43, k1_ordinal1(B_43)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.54  tff(c_82, plain, (![B_56, A_57]: (~r1_tarski(B_56, A_57) | ~r2_hidden(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.26/1.54  tff(c_86, plain, (![B_43]: (~r1_tarski(k1_ordinal1(B_43), B_43))), inference(resolution, [status(thm)], [c_38, c_82])).
% 3.26/1.54  tff(c_561, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_510, c_86])).
% 3.26/1.54  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_561])).
% 3.26/1.54  tff(c_589, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.26/1.54  tff(c_593, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_589, c_46])).
% 3.26/1.54  tff(c_851, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_837, c_593])).
% 3.26/1.54  tff(c_862, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_851])).
% 3.26/1.54  tff(c_866, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_862])).
% 3.26/1.54  tff(c_872, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_866])).
% 3.26/1.54  tff(c_725, plain, (![B_151, A_152]: (r1_ordinal1(B_151, A_152) | r1_ordinal1(A_152, B_151) | ~v3_ordinal1(B_151) | ~v3_ordinal1(A_152))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.54  tff(c_588, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.26/1.54  tff(c_728, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_725, c_588])).
% 3.26/1.54  tff(c_734, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_728])).
% 3.26/1.54  tff(c_739, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_734])).
% 3.26/1.54  tff(c_782, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_739])).
% 3.26/1.54  tff(c_786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_782])).
% 3.26/1.54  tff(c_788, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_734])).
% 3.26/1.54  tff(c_796, plain, (![B_158, A_159]: (r2_hidden(B_158, A_159) | r1_ordinal1(A_159, B_158) | ~v3_ordinal1(B_158) | ~v3_ordinal1(A_159))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.26/1.54  tff(c_36, plain, (![B_43, A_42]: (B_43=A_42 | r2_hidden(A_42, B_43) | ~r2_hidden(A_42, k1_ordinal1(B_43)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.54  tff(c_1062, plain, (![B_204, B_203]: (B_204=B_203 | r2_hidden(B_204, B_203) | r1_ordinal1(k1_ordinal1(B_203), B_204) | ~v3_ordinal1(B_204) | ~v3_ordinal1(k1_ordinal1(B_203)))), inference(resolution, [status(thm)], [c_796, c_36])).
% 3.26/1.54  tff(c_1074, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_1062, c_588])).
% 3.26/1.54  tff(c_1081, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_48, c_1074])).
% 3.26/1.54  tff(c_1082, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1081])).
% 3.26/1.54  tff(c_1086, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1082, c_46])).
% 3.26/1.54  tff(c_1089, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1086])).
% 3.26/1.54  tff(c_1093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_872, c_1089])).
% 3.26/1.54  tff(c_1094, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1081])).
% 3.26/1.54  tff(c_1100, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_593])).
% 3.26/1.54  tff(c_1105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1100])).
% 3.26/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.54  
% 3.26/1.54  Inference rules
% 3.26/1.54  ----------------------
% 3.26/1.54  #Ref     : 0
% 3.26/1.54  #Sup     : 200
% 3.26/1.54  #Fact    : 4
% 3.26/1.54  #Define  : 0
% 3.26/1.54  #Split   : 5
% 3.26/1.54  #Chain   : 0
% 3.26/1.54  #Close   : 0
% 3.26/1.54  
% 3.26/1.54  Ordering : KBO
% 3.26/1.54  
% 3.26/1.54  Simplification rules
% 3.26/1.54  ----------------------
% 3.26/1.54  #Subsume      : 35
% 3.26/1.54  #Demod        : 118
% 3.26/1.54  #Tautology    : 82
% 3.26/1.54  #SimpNegUnit  : 2
% 3.26/1.54  #BackRed      : 20
% 3.26/1.54  
% 3.26/1.54  #Partial instantiations: 0
% 3.26/1.54  #Strategies tried      : 1
% 3.26/1.54  
% 3.26/1.54  Timing (in seconds)
% 3.26/1.54  ----------------------
% 3.26/1.54  Preprocessing        : 0.34
% 3.26/1.54  Parsing              : 0.19
% 3.26/1.54  CNF conversion       : 0.02
% 3.26/1.55  Main loop            : 0.38
% 3.26/1.55  Inferencing          : 0.15
% 3.26/1.55  Reduction            : 0.11
% 3.26/1.55  Demodulation         : 0.07
% 3.26/1.55  BG Simplification    : 0.02
% 3.26/1.55  Subsumption          : 0.07
% 3.26/1.55  Abstraction          : 0.02
% 3.26/1.55  MUC search           : 0.00
% 3.26/1.55  Cooper               : 0.00
% 3.26/1.55  Total                : 0.76
% 3.26/1.55  Index Insertion      : 0.00
% 3.26/1.55  Index Deletion       : 0.00
% 3.26/1.55  Index Matching       : 0.00
% 3.26/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
