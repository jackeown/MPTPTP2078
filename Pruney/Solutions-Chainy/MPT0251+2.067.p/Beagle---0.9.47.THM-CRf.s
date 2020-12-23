%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:55 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.59s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 183 expanded)
%              Number of leaves         :   38 (  78 expanded)
%              Depth                    :   20
%              Number of atoms          :  110 ( 272 expanded)
%              Number of equality atoms :   43 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_90,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_94,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_xboole_0) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_35] : r1_xboole_0(A_35,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    ! [B_29] : r1_tarski(B_29,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_252,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_260,plain,(
    ! [B_29] : k3_xboole_0(B_29,B_29) = B_29 ),
    inference(resolution,[status(thm)],[c_66,c_252])).

tff(c_279,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_283,plain,(
    ! [B_77,C_78] :
      ( ~ r1_xboole_0(B_77,B_77)
      | ~ r2_hidden(C_78,B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_279])).

tff(c_287,plain,(
    ! [C_78] : ~ r2_hidden(C_78,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_283])).

tff(c_393,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_405,plain,(
    ! [B_29] : k5_xboole_0(B_29,B_29) = k4_xboole_0(B_29,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_393])).

tff(c_294,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_315,plain,(
    ! [B_88] : r1_tarski(k1_xboole_0,B_88) ),
    inference(resolution,[status(thm)],[c_294,c_287])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_319,plain,(
    ! [B_88] : k3_xboole_0(k1_xboole_0,B_88) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_315,c_72])).

tff(c_417,plain,(
    ! [B_102] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_393])).

tff(c_32,plain,(
    ! [D_19,A_14,B_15] :
      ( r2_hidden(D_19,A_14)
      | ~ r2_hidden(D_19,k4_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_426,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,k1_xboole_0)
      | ~ r2_hidden(D_19,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_32])).

tff(c_440,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,k1_xboole_0)
      | ~ r2_hidden(D_19,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_426])).

tff(c_452,plain,(
    ! [D_105] : ~ r2_hidden(D_105,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_440])).

tff(c_458,plain,(
    ! [B_106] : r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),B_106) ),
    inference(resolution,[status(thm)],[c_8,c_452])).

tff(c_313,plain,(
    ! [B_87] : r1_tarski(k1_xboole_0,B_87) ),
    inference(resolution,[status(thm)],[c_294,c_287])).

tff(c_344,plain,(
    ! [B_90,A_91] :
      ( B_90 = A_91
      | ~ r1_tarski(B_90,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_351,plain,(
    ! [B_87] :
      ( k1_xboole_0 = B_87
      | ~ r1_tarski(B_87,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_313,c_344])).

tff(c_468,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_458,c_351])).

tff(c_76,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k4_xboole_0(B_37,A_36)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_483,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_76])).

tff(c_487,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_483])).

tff(c_402,plain,(
    ! [B_88] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_393])).

tff(c_512,plain,(
    ! [B_110] : k4_xboole_0(k1_xboole_0,B_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_402])).

tff(c_523,plain,(
    ! [B_110] : k5_xboole_0(B_110,k1_xboole_0) = k2_xboole_0(B_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_76])).

tff(c_528,plain,(
    ! [B_110] : k5_xboole_0(B_110,k1_xboole_0) = B_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_523])).

tff(c_88,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_259,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(k1_tarski(A_48),B_49) = k1_tarski(A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_88,c_252])).

tff(c_2817,plain,(
    ! [A_291,B_292,C_293] :
      ( r2_hidden('#skF_4'(A_291,B_292,C_293),A_291)
      | r2_hidden('#skF_5'(A_291,B_292,C_293),C_293)
      | k4_xboole_0(A_291,B_292) = C_293 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [A_14,B_15,C_16] :
      ( ~ r2_hidden('#skF_4'(A_14,B_15,C_16),B_15)
      | r2_hidden('#skF_5'(A_14,B_15,C_16),C_16)
      | k4_xboole_0(A_14,B_15) = C_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3082,plain,(
    ! [A_305,C_306] :
      ( r2_hidden('#skF_5'(A_305,A_305,C_306),C_306)
      | k4_xboole_0(A_305,A_305) = C_306 ) ),
    inference(resolution,[status(thm)],[c_2817,c_42])).

tff(c_3135,plain,(
    ! [A_305] : k4_xboole_0(A_305,A_305) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3082,c_287])).

tff(c_3138,plain,(
    ! [B_29] : k5_xboole_0(B_29,B_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_405])).

tff(c_381,plain,(
    ! [D_96,B_97,A_98] :
      ( r2_hidden(D_96,B_97)
      | ~ r2_hidden(D_96,k3_xboole_0(A_98,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4714,plain,(
    ! [A_407,B_408,B_409] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_407,B_408),B_409),B_408)
      | r1_tarski(k3_xboole_0(A_407,B_408),B_409) ) ),
    inference(resolution,[status(thm)],[c_8,c_381])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4803,plain,(
    ! [A_410,B_411] : r1_tarski(k3_xboole_0(A_410,B_411),B_411) ),
    inference(resolution,[status(thm)],[c_4714,c_6])).

tff(c_4937,plain,(
    ! [A_412,B_413] : k3_xboole_0(k3_xboole_0(A_412,B_413),B_413) = k3_xboole_0(A_412,B_413) ),
    inference(resolution,[status(thm)],[c_4803,c_72])).

tff(c_68,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5026,plain,(
    ! [A_412,B_413] : k5_xboole_0(k3_xboole_0(A_412,B_413),k3_xboole_0(A_412,B_413)) = k4_xboole_0(k3_xboole_0(A_412,B_413),B_413) ),
    inference(superposition,[status(thm),theory(equality)],[c_4937,c_68])).

tff(c_5161,plain,(
    ! [A_417,B_418] : k4_xboole_0(k3_xboole_0(A_417,B_418),B_418) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3138,c_5026])).

tff(c_5317,plain,(
    ! [A_421,B_422] :
      ( k4_xboole_0(k1_tarski(A_421),B_422) = k1_xboole_0
      | ~ r2_hidden(A_421,B_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_5161])).

tff(c_5358,plain,(
    ! [B_422,A_421] :
      ( k2_xboole_0(B_422,k1_tarski(A_421)) = k5_xboole_0(B_422,k1_xboole_0)
      | ~ r2_hidden(A_421,B_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5317,c_76])).

tff(c_5604,plain,(
    ! [B_430,A_431] :
      ( k2_xboole_0(B_430,k1_tarski(A_431)) = B_430
      | ~ r2_hidden(A_431,B_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_5358])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),'#skF_8') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_96,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_5630,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5604,c_96])).

tff(c_5657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_5630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n010.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 16:03:14 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.59/1.99  
% 5.59/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.59/2.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 5.59/2.00  
% 5.59/2.00  %Foreground sorts:
% 5.59/2.00  
% 5.59/2.00  
% 5.59/2.00  %Background operators:
% 5.59/2.00  
% 5.59/2.00  
% 5.59/2.00  %Foreground operators:
% 5.59/2.00  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.59/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.59/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.59/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.59/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.59/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.59/2.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.59/2.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.59/2.00  tff('#skF_7', type, '#skF_7': $i).
% 5.59/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.59/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.59/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.59/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.59/2.00  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.59/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.59/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.59/2.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.59/2.00  tff('#skF_8', type, '#skF_8': $i).
% 5.59/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.59/2.00  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.59/2.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.59/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.59/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.59/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.59/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.59/2.00  
% 5.59/2.01  tff(f_111, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 5.59/2.01  tff(f_84, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.59/2.01  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.59/2.01  tff(f_90, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.59/2.01  tff(f_80, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.59/2.01  tff(f_88, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.59/2.01  tff(f_74, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.59/2.01  tff(f_82, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.59/2.01  tff(f_53, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.59/2.01  tff(f_92, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.59/2.01  tff(f_104, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.59/2.01  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.59/2.01  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.59/2.01  tff(c_94, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.59/2.01  tff(c_70, plain, (![A_32]: (k2_xboole_0(A_32, k1_xboole_0)=A_32)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.59/2.01  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.59/2.01  tff(c_74, plain, (![A_35]: (r1_xboole_0(A_35, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.59/2.01  tff(c_66, plain, (![B_29]: (r1_tarski(B_29, B_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.59/2.01  tff(c_252, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.59/2.01  tff(c_260, plain, (![B_29]: (k3_xboole_0(B_29, B_29)=B_29)), inference(resolution, [status(thm)], [c_66, c_252])).
% 5.59/2.01  tff(c_279, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.59/2.01  tff(c_283, plain, (![B_77, C_78]: (~r1_xboole_0(B_77, B_77) | ~r2_hidden(C_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_260, c_279])).
% 5.59/2.01  tff(c_287, plain, (![C_78]: (~r2_hidden(C_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_74, c_283])).
% 5.59/2.01  tff(c_393, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.59/2.01  tff(c_405, plain, (![B_29]: (k5_xboole_0(B_29, B_29)=k4_xboole_0(B_29, B_29))), inference(superposition, [status(thm), theory('equality')], [c_260, c_393])).
% 5.59/2.01  tff(c_294, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), A_86) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.59/2.01  tff(c_315, plain, (![B_88]: (r1_tarski(k1_xboole_0, B_88))), inference(resolution, [status(thm)], [c_294, c_287])).
% 5.59/2.01  tff(c_72, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.59/2.01  tff(c_319, plain, (![B_88]: (k3_xboole_0(k1_xboole_0, B_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_315, c_72])).
% 5.59/2.01  tff(c_417, plain, (![B_102]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_102))), inference(superposition, [status(thm), theory('equality')], [c_319, c_393])).
% 5.59/2.01  tff(c_32, plain, (![D_19, A_14, B_15]: (r2_hidden(D_19, A_14) | ~r2_hidden(D_19, k4_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.59/2.01  tff(c_426, plain, (![D_19]: (r2_hidden(D_19, k1_xboole_0) | ~r2_hidden(D_19, k5_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_32])).
% 5.59/2.01  tff(c_440, plain, (![D_19]: (r2_hidden(D_19, k1_xboole_0) | ~r2_hidden(D_19, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_426])).
% 5.59/2.01  tff(c_452, plain, (![D_105]: (~r2_hidden(D_105, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_287, c_440])).
% 5.59/2.01  tff(c_458, plain, (![B_106]: (r1_tarski(k4_xboole_0(k1_xboole_0, k1_xboole_0), B_106))), inference(resolution, [status(thm)], [c_8, c_452])).
% 5.59/2.01  tff(c_313, plain, (![B_87]: (r1_tarski(k1_xboole_0, B_87))), inference(resolution, [status(thm)], [c_294, c_287])).
% 5.59/2.01  tff(c_344, plain, (![B_90, A_91]: (B_90=A_91 | ~r1_tarski(B_90, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.59/2.01  tff(c_351, plain, (![B_87]: (k1_xboole_0=B_87 | ~r1_tarski(B_87, k1_xboole_0))), inference(resolution, [status(thm)], [c_313, c_344])).
% 5.59/2.01  tff(c_468, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_458, c_351])).
% 5.59/2.01  tff(c_76, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k4_xboole_0(B_37, A_36))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.59/2.01  tff(c_483, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_468, c_76])).
% 5.59/2.01  tff(c_487, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_483])).
% 5.59/2.01  tff(c_402, plain, (![B_88]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_88))), inference(superposition, [status(thm), theory('equality')], [c_319, c_393])).
% 5.59/2.01  tff(c_512, plain, (![B_110]: (k4_xboole_0(k1_xboole_0, B_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_487, c_402])).
% 5.59/2.01  tff(c_523, plain, (![B_110]: (k5_xboole_0(B_110, k1_xboole_0)=k2_xboole_0(B_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_512, c_76])).
% 5.59/2.01  tff(c_528, plain, (![B_110]: (k5_xboole_0(B_110, k1_xboole_0)=B_110)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_523])).
% 5.59/2.01  tff(c_88, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.59/2.01  tff(c_259, plain, (![A_48, B_49]: (k3_xboole_0(k1_tarski(A_48), B_49)=k1_tarski(A_48) | ~r2_hidden(A_48, B_49))), inference(resolution, [status(thm)], [c_88, c_252])).
% 5.59/2.01  tff(c_2817, plain, (![A_291, B_292, C_293]: (r2_hidden('#skF_4'(A_291, B_292, C_293), A_291) | r2_hidden('#skF_5'(A_291, B_292, C_293), C_293) | k4_xboole_0(A_291, B_292)=C_293)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.59/2.01  tff(c_42, plain, (![A_14, B_15, C_16]: (~r2_hidden('#skF_4'(A_14, B_15, C_16), B_15) | r2_hidden('#skF_5'(A_14, B_15, C_16), C_16) | k4_xboole_0(A_14, B_15)=C_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.59/2.01  tff(c_3082, plain, (![A_305, C_306]: (r2_hidden('#skF_5'(A_305, A_305, C_306), C_306) | k4_xboole_0(A_305, A_305)=C_306)), inference(resolution, [status(thm)], [c_2817, c_42])).
% 5.59/2.01  tff(c_3135, plain, (![A_305]: (k4_xboole_0(A_305, A_305)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3082, c_287])).
% 5.59/2.01  tff(c_3138, plain, (![B_29]: (k5_xboole_0(B_29, B_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_405])).
% 5.59/2.01  tff(c_381, plain, (![D_96, B_97, A_98]: (r2_hidden(D_96, B_97) | ~r2_hidden(D_96, k3_xboole_0(A_98, B_97)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.59/2.01  tff(c_4714, plain, (![A_407, B_408, B_409]: (r2_hidden('#skF_1'(k3_xboole_0(A_407, B_408), B_409), B_408) | r1_tarski(k3_xboole_0(A_407, B_408), B_409))), inference(resolution, [status(thm)], [c_8, c_381])).
% 5.59/2.01  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.59/2.01  tff(c_4803, plain, (![A_410, B_411]: (r1_tarski(k3_xboole_0(A_410, B_411), B_411))), inference(resolution, [status(thm)], [c_4714, c_6])).
% 5.59/2.01  tff(c_4937, plain, (![A_412, B_413]: (k3_xboole_0(k3_xboole_0(A_412, B_413), B_413)=k3_xboole_0(A_412, B_413))), inference(resolution, [status(thm)], [c_4803, c_72])).
% 5.59/2.01  tff(c_68, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.59/2.01  tff(c_5026, plain, (![A_412, B_413]: (k5_xboole_0(k3_xboole_0(A_412, B_413), k3_xboole_0(A_412, B_413))=k4_xboole_0(k3_xboole_0(A_412, B_413), B_413))), inference(superposition, [status(thm), theory('equality')], [c_4937, c_68])).
% 5.59/2.01  tff(c_5161, plain, (![A_417, B_418]: (k4_xboole_0(k3_xboole_0(A_417, B_418), B_418)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3138, c_5026])).
% 5.59/2.01  tff(c_5317, plain, (![A_421, B_422]: (k4_xboole_0(k1_tarski(A_421), B_422)=k1_xboole_0 | ~r2_hidden(A_421, B_422))), inference(superposition, [status(thm), theory('equality')], [c_259, c_5161])).
% 5.59/2.01  tff(c_5358, plain, (![B_422, A_421]: (k2_xboole_0(B_422, k1_tarski(A_421))=k5_xboole_0(B_422, k1_xboole_0) | ~r2_hidden(A_421, B_422))), inference(superposition, [status(thm), theory('equality')], [c_5317, c_76])).
% 5.59/2.01  tff(c_5604, plain, (![B_430, A_431]: (k2_xboole_0(B_430, k1_tarski(A_431))=B_430 | ~r2_hidden(A_431, B_430))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_5358])).
% 5.59/2.01  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.59/2.01  tff(c_92, plain, (k2_xboole_0(k1_tarski('#skF_7'), '#skF_8')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.59/2.01  tff(c_96, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_92])).
% 5.59/2.01  tff(c_5630, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5604, c_96])).
% 5.59/2.01  tff(c_5657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_5630])).
% 5.59/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.59/2.01  
% 5.59/2.01  Inference rules
% 5.59/2.01  ----------------------
% 5.59/2.01  #Ref     : 0
% 5.59/2.01  #Sup     : 1330
% 5.59/2.01  #Fact    : 0
% 5.59/2.01  #Define  : 0
% 5.59/2.01  #Split   : 0
% 5.59/2.01  #Chain   : 0
% 5.59/2.01  #Close   : 0
% 5.59/2.01  
% 5.59/2.01  Ordering : KBO
% 5.59/2.01  
% 5.59/2.01  Simplification rules
% 5.59/2.01  ----------------------
% 5.59/2.01  #Subsume      : 484
% 5.59/2.01  #Demod        : 326
% 5.59/2.01  #Tautology    : 337
% 5.59/2.01  #SimpNegUnit  : 46
% 5.59/2.01  #BackRed      : 6
% 5.59/2.01  
% 5.59/2.01  #Partial instantiations: 0
% 5.59/2.01  #Strategies tried      : 1
% 5.59/2.01  
% 5.59/2.01  Timing (in seconds)
% 5.59/2.01  ----------------------
% 5.59/2.01  Preprocessing        : 0.35
% 5.59/2.01  Parsing              : 0.18
% 5.59/2.01  CNF conversion       : 0.03
% 5.59/2.01  Main loop            : 1.02
% 5.59/2.01  Inferencing          : 0.34
% 5.59/2.01  Reduction            : 0.32
% 5.59/2.01  Demodulation         : 0.22
% 5.59/2.02  BG Simplification    : 0.04
% 5.59/2.02  Subsumption          : 0.26
% 5.59/2.02  Abstraction          : 0.05
% 5.59/2.02  MUC search           : 0.00
% 5.59/2.02  Cooper               : 0.00
% 5.59/2.02  Total                : 1.41
% 5.59/2.02  Index Insertion      : 0.00
% 5.59/2.02  Index Deletion       : 0.00
% 5.59/2.02  Index Matching       : 0.00
% 5.59/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
