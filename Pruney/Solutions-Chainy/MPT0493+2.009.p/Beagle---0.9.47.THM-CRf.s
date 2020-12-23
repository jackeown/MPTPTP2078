%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:37 EST 2020

% Result     : Theorem 10.65s
% Output     : CNFRefutation 10.74s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 252 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  120 ( 456 expanded)
%              Number of equality atoms :   40 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_46,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_137,plain,(
    ! [D_44,A_45,B_46] :
      ( r2_hidden(D_44,A_45)
      | ~ r2_hidden(D_44,k4_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1538,plain,(
    ! [A_135,B_136,B_137] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_135,B_136),B_137),A_135)
      | r1_tarski(k4_xboole_0(A_135,B_136),B_137) ) ),
    inference(resolution,[status(thm)],[c_8,c_137])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1601,plain,(
    ! [A_135,B_136] : r1_tarski(k4_xboole_0(A_135,B_136),A_135) ),
    inference(resolution,[status(thm)],[c_1538,c_6])).

tff(c_36,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_167,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_146])).

tff(c_641,plain,(
    ! [A_85,B_86,C_87] :
      ( r2_hidden('#skF_2'(A_85,B_86,C_87),A_85)
      | r2_hidden('#skF_3'(A_85,B_86,C_87),C_87)
      | k4_xboole_0(A_85,B_86) = C_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),B_9)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_644,plain,(
    ! [A_85,C_87] :
      ( r2_hidden('#skF_3'(A_85,A_85,C_87),C_87)
      | k4_xboole_0(A_85,A_85) = C_87 ) ),
    inference(resolution,[status(thm)],[c_641,c_24])).

tff(c_710,plain,(
    ! [A_85,C_87] :
      ( r2_hidden('#skF_3'(A_85,A_85,C_87),C_87)
      | k3_xboole_0(A_85,k1_xboole_0) = C_87 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_644])).

tff(c_728,plain,(
    ! [A_88,C_89] :
      ( r2_hidden('#skF_3'(A_88,A_88,C_89),C_89)
      | k3_xboole_0(A_88,k1_xboole_0) = C_89 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_644])).

tff(c_114,plain,(
    ! [D_35,B_36,A_37] :
      ( ~ r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k4_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [D_35,A_17] :
      ( ~ r2_hidden(D_35,k1_xboole_0)
      | ~ r2_hidden(D_35,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_114])).

tff(c_800,plain,(
    ! [A_92,A_93] :
      ( ~ r2_hidden('#skF_3'(A_92,A_92,k1_xboole_0),A_93)
      | k3_xboole_0(A_92,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_728,c_117])).

tff(c_811,plain,(
    ! [A_85] : k3_xboole_0(A_85,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_710,c_800])).

tff(c_830,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_167])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_452,plain,(
    ! [D_72,A_73,B_74] :
      ( r2_hidden(D_72,k4_xboole_0(A_73,B_74))
      | r2_hidden(D_72,B_74)
      | ~ r2_hidden(D_72,A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4632,plain,(
    ! [A_252,A_253,B_254] :
      ( r1_tarski(A_252,k4_xboole_0(A_253,B_254))
      | r2_hidden('#skF_1'(A_252,k4_xboole_0(A_253,B_254)),B_254)
      | ~ r2_hidden('#skF_1'(A_252,k4_xboole_0(A_253,B_254)),A_253) ) ),
    inference(resolution,[status(thm)],[c_452,c_6])).

tff(c_4701,plain,(
    ! [A_255,B_256] :
      ( r2_hidden('#skF_1'(A_255,k4_xboole_0(A_255,B_256)),B_256)
      | r1_tarski(A_255,k4_xboole_0(A_255,B_256)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4632])).

tff(c_120,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    ! [A_8,B_9,B_43] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_8,B_9),B_43),B_9)
      | r1_tarski(k4_xboole_0(A_8,B_9),B_43) ) ),
    inference(resolution,[status(thm)],[c_120,c_12])).

tff(c_4813,plain,(
    ! [A_257,B_258] : r1_tarski(k4_xboole_0(A_257,B_258),k4_xboole_0(k4_xboole_0(A_257,B_258),B_258)) ),
    inference(resolution,[status(thm)],[c_4701,c_136])).

tff(c_1611,plain,(
    ! [A_138,B_139] : r1_tarski(k4_xboole_0(A_138,B_139),A_138) ),
    inference(resolution,[status(thm)],[c_1538,c_6])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1643,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(A_138,B_139) = A_138
      | ~ r1_tarski(A_138,k4_xboole_0(A_138,B_139)) ) ),
    inference(resolution,[status(thm)],[c_1611,c_28])).

tff(c_4897,plain,(
    ! [A_259,B_260] : k4_xboole_0(k4_xboole_0(A_259,B_260),B_260) = k4_xboole_0(A_259,B_260) ),
    inference(resolution,[status(thm)],[c_4813,c_1643])).

tff(c_4967,plain,(
    ! [A_259,B_260] : k4_xboole_0(k4_xboole_0(A_259,B_260),k4_xboole_0(A_259,B_260)) = k3_xboole_0(k4_xboole_0(A_259,B_260),B_260) ),
    inference(superposition,[status(thm),theory(equality)],[c_4897,c_38])).

tff(c_5154,plain,(
    ! [B_264,A_265] : k3_xboole_0(B_264,k4_xboole_0(A_265,B_264)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_2,c_4967])).

tff(c_149,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_38])).

tff(c_5248,plain,(
    ! [B_264,A_265] : k3_xboole_0(B_264,k4_xboole_0(B_264,k4_xboole_0(A_265,B_264))) = k4_xboole_0(B_264,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5154,c_149])).

tff(c_5327,plain,(
    ! [B_264,A_265] : k3_xboole_0(B_264,k4_xboole_0(B_264,k4_xboole_0(A_265,B_264))) = B_264 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5248])).

tff(c_5752,plain,(
    ! [B_272,A_273] : k3_xboole_0(B_272,k4_xboole_0(B_272,k4_xboole_0(A_273,B_272))) = B_272 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5248])).

tff(c_1647,plain,(
    ! [A_140,B_141] : r1_tarski(k3_xboole_0(A_140,B_141),A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1611])).

tff(c_1686,plain,(
    ! [B_142,A_143] : r1_tarski(k3_xboole_0(B_142,A_143),A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1647])).

tff(c_1721,plain,(
    ! [B_142,A_143] :
      ( k3_xboole_0(B_142,A_143) = A_143
      | ~ r1_tarski(A_143,k3_xboole_0(B_142,A_143)) ) ),
    inference(resolution,[status(thm)],[c_1686,c_28])).

tff(c_5825,plain,(
    ! [B_272,A_273] :
      ( k3_xboole_0(B_272,k4_xboole_0(B_272,k4_xboole_0(A_273,B_272))) = k4_xboole_0(B_272,k4_xboole_0(A_273,B_272))
      | ~ r1_tarski(k4_xboole_0(B_272,k4_xboole_0(A_273,B_272)),B_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5752,c_1721])).

tff(c_5928,plain,(
    ! [B_272,A_273] : k4_xboole_0(B_272,k4_xboole_0(A_273,B_272)) = B_272 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1601,c_5327,c_5825])).

tff(c_4699,plain,(
    ! [A_3,B_254] :
      ( r2_hidden('#skF_1'(A_3,k4_xboole_0(A_3,B_254)),B_254)
      | r1_tarski(A_3,k4_xboole_0(A_3,B_254)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4632])).

tff(c_260,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1380,plain,(
    ! [A_121,B_122,B_123] :
      ( r2_hidden('#skF_1'(A_121,B_122),B_123)
      | ~ r1_tarski(A_121,B_123)
      | r1_tarski(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_8,c_260])).

tff(c_22608,plain,(
    ! [A_495,B_496,B_497,A_498] :
      ( ~ r2_hidden('#skF_1'(A_495,B_496),B_497)
      | ~ r1_tarski(A_495,k4_xboole_0(A_498,B_497))
      | r1_tarski(A_495,B_496) ) ),
    inference(resolution,[status(thm)],[c_1380,c_12])).

tff(c_22649,plain,(
    ! [A_499,A_500,B_501] :
      ( ~ r1_tarski(A_499,k4_xboole_0(A_500,B_501))
      | r1_tarski(A_499,k4_xboole_0(A_499,B_501)) ) ),
    inference(resolution,[status(thm)],[c_4699,c_22608])).

tff(c_22733,plain,(
    ! [A_502,B_503,A_504] :
      ( ~ r1_tarski(A_502,B_503)
      | r1_tarski(A_502,k4_xboole_0(A_502,k4_xboole_0(A_504,B_503))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5928,c_22649])).

tff(c_22875,plain,(
    ! [A_505,B_506] :
      ( ~ r1_tarski(A_505,B_506)
      | r1_tarski(A_505,k3_xboole_0(A_505,B_506)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_22733])).

tff(c_1959,plain,(
    ! [B_161,A_162] :
      ( k3_xboole_0(B_161,A_162) = A_162
      | ~ r1_tarski(A_162,k3_xboole_0(B_161,A_162)) ) ),
    inference(resolution,[status(thm)],[c_1686,c_28])).

tff(c_1981,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(B_2,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1959])).

tff(c_23132,plain,(
    ! [B_509,A_510] :
      ( k3_xboole_0(B_509,A_510) = A_510
      | ~ r1_tarski(A_510,B_509) ) ),
    inference(resolution,[status(thm)],[c_22875,c_1981])).

tff(c_23237,plain,(
    k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_23132])).

tff(c_44,plain,(
    ! [B_25,A_24] :
      ( k3_xboole_0(k1_relat_1(B_25),A_24) = k1_relat_1(k7_relat_1(B_25,A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_23468,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_23237,c_44])).

tff(c_23544,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_23468])).

tff(c_23546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_23544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.65/4.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/4.33  
% 10.74/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/4.34  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 10.74/4.34  
% 10.74/4.34  %Foreground sorts:
% 10.74/4.34  
% 10.74/4.34  
% 10.74/4.34  %Background operators:
% 10.74/4.34  
% 10.74/4.34  
% 10.74/4.34  %Foreground operators:
% 10.74/4.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.74/4.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.74/4.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.74/4.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.74/4.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.74/4.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.74/4.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.74/4.34  tff('#skF_5', type, '#skF_5': $i).
% 10.74/4.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.74/4.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.74/4.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.74/4.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.74/4.34  tff('#skF_4', type, '#skF_4': $i).
% 10.74/4.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.74/4.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.74/4.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.74/4.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.74/4.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.74/4.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.74/4.34  
% 10.74/4.35  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 10.74/4.35  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.74/4.35  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.74/4.35  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.74/4.35  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.74/4.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.74/4.35  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.74/4.35  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 10.74/4.35  tff(c_46, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.74/4.35  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.74/4.35  tff(c_48, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.74/4.35  tff(c_38, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.74/4.35  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.74/4.35  tff(c_137, plain, (![D_44, A_45, B_46]: (r2_hidden(D_44, A_45) | ~r2_hidden(D_44, k4_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.74/4.35  tff(c_1538, plain, (![A_135, B_136, B_137]: (r2_hidden('#skF_1'(k4_xboole_0(A_135, B_136), B_137), A_135) | r1_tarski(k4_xboole_0(A_135, B_136), B_137))), inference(resolution, [status(thm)], [c_8, c_137])).
% 10.74/4.35  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.74/4.35  tff(c_1601, plain, (![A_135, B_136]: (r1_tarski(k4_xboole_0(A_135, B_136), A_135))), inference(resolution, [status(thm)], [c_1538, c_6])).
% 10.74/4.35  tff(c_36, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.74/4.35  tff(c_146, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.74/4.35  tff(c_167, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_146])).
% 10.74/4.35  tff(c_641, plain, (![A_85, B_86, C_87]: (r2_hidden('#skF_2'(A_85, B_86, C_87), A_85) | r2_hidden('#skF_3'(A_85, B_86, C_87), C_87) | k4_xboole_0(A_85, B_86)=C_87)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.74/4.35  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), B_9) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.74/4.35  tff(c_644, plain, (![A_85, C_87]: (r2_hidden('#skF_3'(A_85, A_85, C_87), C_87) | k4_xboole_0(A_85, A_85)=C_87)), inference(resolution, [status(thm)], [c_641, c_24])).
% 10.74/4.35  tff(c_710, plain, (![A_85, C_87]: (r2_hidden('#skF_3'(A_85, A_85, C_87), C_87) | k3_xboole_0(A_85, k1_xboole_0)=C_87)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_644])).
% 10.74/4.35  tff(c_728, plain, (![A_88, C_89]: (r2_hidden('#skF_3'(A_88, A_88, C_89), C_89) | k3_xboole_0(A_88, k1_xboole_0)=C_89)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_644])).
% 10.74/4.35  tff(c_114, plain, (![D_35, B_36, A_37]: (~r2_hidden(D_35, B_36) | ~r2_hidden(D_35, k4_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.74/4.35  tff(c_117, plain, (![D_35, A_17]: (~r2_hidden(D_35, k1_xboole_0) | ~r2_hidden(D_35, A_17))), inference(superposition, [status(thm), theory('equality')], [c_36, c_114])).
% 10.74/4.35  tff(c_800, plain, (![A_92, A_93]: (~r2_hidden('#skF_3'(A_92, A_92, k1_xboole_0), A_93) | k3_xboole_0(A_92, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_728, c_117])).
% 10.74/4.35  tff(c_811, plain, (![A_85]: (k3_xboole_0(A_85, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_710, c_800])).
% 10.74/4.35  tff(c_830, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_811, c_167])).
% 10.74/4.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.74/4.35  tff(c_452, plain, (![D_72, A_73, B_74]: (r2_hidden(D_72, k4_xboole_0(A_73, B_74)) | r2_hidden(D_72, B_74) | ~r2_hidden(D_72, A_73))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.74/4.35  tff(c_4632, plain, (![A_252, A_253, B_254]: (r1_tarski(A_252, k4_xboole_0(A_253, B_254)) | r2_hidden('#skF_1'(A_252, k4_xboole_0(A_253, B_254)), B_254) | ~r2_hidden('#skF_1'(A_252, k4_xboole_0(A_253, B_254)), A_253))), inference(resolution, [status(thm)], [c_452, c_6])).
% 10.74/4.35  tff(c_4701, plain, (![A_255, B_256]: (r2_hidden('#skF_1'(A_255, k4_xboole_0(A_255, B_256)), B_256) | r1_tarski(A_255, k4_xboole_0(A_255, B_256)))), inference(resolution, [status(thm)], [c_8, c_4632])).
% 10.74/4.35  tff(c_120, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), A_42) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.74/4.35  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.74/4.35  tff(c_136, plain, (![A_8, B_9, B_43]: (~r2_hidden('#skF_1'(k4_xboole_0(A_8, B_9), B_43), B_9) | r1_tarski(k4_xboole_0(A_8, B_9), B_43))), inference(resolution, [status(thm)], [c_120, c_12])).
% 10.74/4.35  tff(c_4813, plain, (![A_257, B_258]: (r1_tarski(k4_xboole_0(A_257, B_258), k4_xboole_0(k4_xboole_0(A_257, B_258), B_258)))), inference(resolution, [status(thm)], [c_4701, c_136])).
% 10.74/4.35  tff(c_1611, plain, (![A_138, B_139]: (r1_tarski(k4_xboole_0(A_138, B_139), A_138))), inference(resolution, [status(thm)], [c_1538, c_6])).
% 10.74/4.35  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.74/4.35  tff(c_1643, plain, (![A_138, B_139]: (k4_xboole_0(A_138, B_139)=A_138 | ~r1_tarski(A_138, k4_xboole_0(A_138, B_139)))), inference(resolution, [status(thm)], [c_1611, c_28])).
% 10.74/4.35  tff(c_4897, plain, (![A_259, B_260]: (k4_xboole_0(k4_xboole_0(A_259, B_260), B_260)=k4_xboole_0(A_259, B_260))), inference(resolution, [status(thm)], [c_4813, c_1643])).
% 10.74/4.35  tff(c_4967, plain, (![A_259, B_260]: (k4_xboole_0(k4_xboole_0(A_259, B_260), k4_xboole_0(A_259, B_260))=k3_xboole_0(k4_xboole_0(A_259, B_260), B_260))), inference(superposition, [status(thm), theory('equality')], [c_4897, c_38])).
% 10.74/4.35  tff(c_5154, plain, (![B_264, A_265]: (k3_xboole_0(B_264, k4_xboole_0(A_265, B_264))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_830, c_2, c_4967])).
% 10.74/4.35  tff(c_149, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k3_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_38])).
% 10.74/4.35  tff(c_5248, plain, (![B_264, A_265]: (k3_xboole_0(B_264, k4_xboole_0(B_264, k4_xboole_0(A_265, B_264)))=k4_xboole_0(B_264, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5154, c_149])).
% 10.74/4.35  tff(c_5327, plain, (![B_264, A_265]: (k3_xboole_0(B_264, k4_xboole_0(B_264, k4_xboole_0(A_265, B_264)))=B_264)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5248])).
% 10.74/4.35  tff(c_5752, plain, (![B_272, A_273]: (k3_xboole_0(B_272, k4_xboole_0(B_272, k4_xboole_0(A_273, B_272)))=B_272)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5248])).
% 10.74/4.35  tff(c_1647, plain, (![A_140, B_141]: (r1_tarski(k3_xboole_0(A_140, B_141), A_140))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1611])).
% 10.74/4.35  tff(c_1686, plain, (![B_142, A_143]: (r1_tarski(k3_xboole_0(B_142, A_143), A_143))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1647])).
% 10.74/4.35  tff(c_1721, plain, (![B_142, A_143]: (k3_xboole_0(B_142, A_143)=A_143 | ~r1_tarski(A_143, k3_xboole_0(B_142, A_143)))), inference(resolution, [status(thm)], [c_1686, c_28])).
% 10.74/4.35  tff(c_5825, plain, (![B_272, A_273]: (k3_xboole_0(B_272, k4_xboole_0(B_272, k4_xboole_0(A_273, B_272)))=k4_xboole_0(B_272, k4_xboole_0(A_273, B_272)) | ~r1_tarski(k4_xboole_0(B_272, k4_xboole_0(A_273, B_272)), B_272))), inference(superposition, [status(thm), theory('equality')], [c_5752, c_1721])).
% 10.74/4.35  tff(c_5928, plain, (![B_272, A_273]: (k4_xboole_0(B_272, k4_xboole_0(A_273, B_272))=B_272)), inference(demodulation, [status(thm), theory('equality')], [c_1601, c_5327, c_5825])).
% 10.74/4.35  tff(c_4699, plain, (![A_3, B_254]: (r2_hidden('#skF_1'(A_3, k4_xboole_0(A_3, B_254)), B_254) | r1_tarski(A_3, k4_xboole_0(A_3, B_254)))), inference(resolution, [status(thm)], [c_8, c_4632])).
% 10.74/4.35  tff(c_260, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.74/4.35  tff(c_1380, plain, (![A_121, B_122, B_123]: (r2_hidden('#skF_1'(A_121, B_122), B_123) | ~r1_tarski(A_121, B_123) | r1_tarski(A_121, B_122))), inference(resolution, [status(thm)], [c_8, c_260])).
% 10.74/4.35  tff(c_22608, plain, (![A_495, B_496, B_497, A_498]: (~r2_hidden('#skF_1'(A_495, B_496), B_497) | ~r1_tarski(A_495, k4_xboole_0(A_498, B_497)) | r1_tarski(A_495, B_496))), inference(resolution, [status(thm)], [c_1380, c_12])).
% 10.74/4.35  tff(c_22649, plain, (![A_499, A_500, B_501]: (~r1_tarski(A_499, k4_xboole_0(A_500, B_501)) | r1_tarski(A_499, k4_xboole_0(A_499, B_501)))), inference(resolution, [status(thm)], [c_4699, c_22608])).
% 10.74/4.35  tff(c_22733, plain, (![A_502, B_503, A_504]: (~r1_tarski(A_502, B_503) | r1_tarski(A_502, k4_xboole_0(A_502, k4_xboole_0(A_504, B_503))))), inference(superposition, [status(thm), theory('equality')], [c_5928, c_22649])).
% 10.74/4.35  tff(c_22875, plain, (![A_505, B_506]: (~r1_tarski(A_505, B_506) | r1_tarski(A_505, k3_xboole_0(A_505, B_506)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_22733])).
% 10.74/4.35  tff(c_1959, plain, (![B_161, A_162]: (k3_xboole_0(B_161, A_162)=A_162 | ~r1_tarski(A_162, k3_xboole_0(B_161, A_162)))), inference(resolution, [status(thm)], [c_1686, c_28])).
% 10.74/4.35  tff(c_1981, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(B_2, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1959])).
% 10.74/4.35  tff(c_23132, plain, (![B_509, A_510]: (k3_xboole_0(B_509, A_510)=A_510 | ~r1_tarski(A_510, B_509))), inference(resolution, [status(thm)], [c_22875, c_1981])).
% 10.74/4.35  tff(c_23237, plain, (k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_23132])).
% 10.74/4.35  tff(c_44, plain, (![B_25, A_24]: (k3_xboole_0(k1_relat_1(B_25), A_24)=k1_relat_1(k7_relat_1(B_25, A_24)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.74/4.35  tff(c_23468, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_23237, c_44])).
% 10.74/4.35  tff(c_23544, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_23468])).
% 10.74/4.35  tff(c_23546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_23544])).
% 10.74/4.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/4.35  
% 10.74/4.35  Inference rules
% 10.74/4.35  ----------------------
% 10.74/4.35  #Ref     : 0
% 10.74/4.35  #Sup     : 5826
% 10.74/4.35  #Fact    : 0
% 10.74/4.35  #Define  : 0
% 10.74/4.35  #Split   : 1
% 10.74/4.35  #Chain   : 0
% 10.74/4.35  #Close   : 0
% 10.74/4.35  
% 10.74/4.35  Ordering : KBO
% 10.74/4.35  
% 10.74/4.35  Simplification rules
% 10.74/4.35  ----------------------
% 10.74/4.35  #Subsume      : 1235
% 10.74/4.35  #Demod        : 6976
% 10.74/4.35  #Tautology    : 2117
% 10.74/4.35  #SimpNegUnit  : 2
% 10.74/4.35  #BackRed      : 9
% 10.74/4.35  
% 10.74/4.35  #Partial instantiations: 0
% 10.74/4.35  #Strategies tried      : 1
% 10.74/4.35  
% 10.74/4.35  Timing (in seconds)
% 10.74/4.35  ----------------------
% 10.74/4.36  Preprocessing        : 0.31
% 10.74/4.36  Parsing              : 0.16
% 10.74/4.36  CNF conversion       : 0.02
% 10.74/4.36  Main loop            : 3.27
% 10.74/4.36  Inferencing          : 0.67
% 10.74/4.36  Reduction            : 1.58
% 10.74/4.36  Demodulation         : 1.38
% 10.74/4.36  BG Simplification    : 0.08
% 10.74/4.36  Subsumption          : 0.77
% 10.74/4.36  Abstraction          : 0.13
% 10.74/4.36  MUC search           : 0.00
% 10.74/4.36  Cooper               : 0.00
% 10.74/4.36  Total                : 3.62
% 10.74/4.36  Index Insertion      : 0.00
% 10.74/4.36  Index Deletion       : 0.00
% 10.74/4.36  Index Matching       : 0.00
% 10.74/4.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
