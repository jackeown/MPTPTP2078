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
% DateTime   : Thu Dec  3 09:57:53 EST 2020

% Result     : Theorem 44.49s
% Output     : CNFRefutation 44.49s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 783 expanded)
%              Number of leaves         :   35 ( 275 expanded)
%              Depth                    :   27
%              Number of atoms          :  171 (1180 expanded)
%              Number of equality atoms :   83 ( 457 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(C,k3_tarski(k2_xboole_0(A,B)))
          & ! [D] :
              ( r2_hidden(D,B)
             => r1_xboole_0(D,C) ) )
       => r1_tarski(C,k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(c_48,plain,(
    ~ r1_tarski('#skF_6',k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_364,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k4_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_436,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k3_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_364])).

tff(c_481,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_28])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_516,plain,(
    ! [C_14] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_14,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_14])).

tff(c_523,plain,(
    ! [C_94] : ~ r2_hidden(C_94,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_516])).

tff(c_528,plain,(
    ! [B_4] : r1_tarski(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_523])).

tff(c_20,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_160,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,B_58)
      | ~ r1_tarski(A_57,k4_xboole_0(B_58,C_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_168,plain,(
    ! [B_58,C_59] : r1_tarski(k4_xboole_0(B_58,C_59),B_58) ),
    inference(resolution,[status(thm)],[c_20,c_160])).

tff(c_418,plain,(
    ! [A_89,B_90] : r1_tarski(k3_xboole_0(A_89,B_90),A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_168])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_435,plain,(
    ! [A_89,B_90] : k2_xboole_0(k3_xboole_0(A_89,B_90),A_89) = A_89 ),
    inference(resolution,[status(thm)],[c_418,c_26])).

tff(c_529,plain,(
    ! [B_95] : r1_tarski(k1_xboole_0,B_95) ),
    inference(resolution,[status(thm)],[c_8,c_523])).

tff(c_552,plain,(
    ! [B_98] : k2_xboole_0(k1_xboole_0,B_98) = B_98 ),
    inference(resolution,[status(thm)],[c_529,c_26])).

tff(c_169,plain,(
    ! [B_60,C_61] : r1_tarski(k4_xboole_0(B_60,C_61),B_60) ),
    inference(resolution,[status(thm)],[c_20,c_160])).

tff(c_214,plain,(
    ! [B_65,C_66] : k2_xboole_0(k4_xboole_0(B_65,C_66),B_65) = B_65 ),
    inference(resolution,[status(thm)],[c_169,c_26])).

tff(c_223,plain,(
    ! [B_65,C_66] : k2_xboole_0(B_65,k4_xboole_0(B_65,C_66)) = B_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_2])).

tff(c_559,plain,(
    ! [C_66] : k4_xboole_0(k1_xboole_0,C_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_223])).

tff(c_493,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93),A_92)
      | r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1565,plain,(
    ! [A_151,B_152,B_153] :
      ( ~ r1_xboole_0(A_151,B_152)
      | r1_tarski(k3_xboole_0(A_151,B_152),B_153) ) ),
    inference(resolution,[status(thm)],[c_493,c_14])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_543,plain,(
    ! [B_95] :
      ( k1_xboole_0 = B_95
      | ~ r1_tarski(B_95,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_529,c_16])).

tff(c_2390,plain,(
    ! [A_201,B_202] :
      ( k3_xboole_0(A_201,B_202) = k1_xboole_0
      | ~ r1_xboole_0(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_1565,c_543])).

tff(c_2487,plain,(
    ! [A_28] : k3_xboole_0(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_2390])).

tff(c_414,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_364])).

tff(c_2645,plain,(
    ! [A_205] : k4_xboole_0(A_205,A_205) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2487,c_414])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k4_xboole_0(A_23,B_24),C_25) = k4_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2686,plain,(
    ! [A_205,C_25] : k4_xboole_0(A_205,k2_xboole_0(A_205,C_25)) = k4_xboole_0(k1_xboole_0,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_2645,c_30])).

tff(c_3007,plain,(
    ! [A_214,C_215] : k4_xboole_0(A_214,k2_xboole_0(A_214,C_215)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_2686])).

tff(c_32,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3058,plain,(
    ! [A_214,C_215] : k3_xboole_0(A_214,k2_xboole_0(A_214,C_215)) = k4_xboole_0(A_214,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3007,c_32])).

tff(c_3696,plain,(
    ! [A_224,C_225] : k3_xboole_0(A_224,k2_xboole_0(A_224,C_225)) = A_224 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3058])).

tff(c_29661,plain,(
    ! [A_515,B_516] : k3_xboole_0(k3_xboole_0(A_515,B_516),A_515) = k3_xboole_0(A_515,B_516) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_3696])).

tff(c_827,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_3'(A_108,B_109),A_108)
      | r1_xboole_0(k3_tarski(A_108),B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    ! [D_41] :
      ( r1_xboole_0(D_41,'#skF_6')
      | ~ r2_hidden(D_41,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_845,plain,(
    ! [B_109] :
      ( r1_xboole_0('#skF_3'('#skF_5',B_109),'#skF_6')
      | r1_xboole_0(k3_tarski('#skF_5'),B_109) ) ),
    inference(resolution,[status(thm)],[c_827,c_50])).

tff(c_4243,plain,(
    ! [B_236] :
      ( k3_xboole_0(k3_tarski('#skF_5'),B_236) = k1_xboole_0
      | r1_xboole_0('#skF_3'('#skF_5',B_236),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_845,c_2390])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( ~ r1_xboole_0('#skF_3'(A_37,B_38),B_38)
      | r1_xboole_0(k3_tarski(A_37),B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4251,plain,
    ( r1_xboole_0(k3_tarski('#skF_5'),'#skF_6')
    | k3_xboole_0(k3_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4243,c_44])).

tff(c_5702,plain,(
    k3_xboole_0(k3_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4251])).

tff(c_38,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_399,plain,(
    ! [A_87,B_88] : k5_xboole_0(k4_xboole_0(A_87,B_88),k3_xboole_0(A_87,B_88)) = k2_xboole_0(k4_xboole_0(A_87,B_88),A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_38])).

tff(c_5988,plain,(
    ! [A_277,B_278] : k5_xboole_0(k4_xboole_0(A_277,B_278),k3_xboole_0(A_277,B_278)) = A_277 ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_2,c_399])).

tff(c_5997,plain,(
    k5_xboole_0(k4_xboole_0(k3_tarski('#skF_5'),'#skF_6'),k1_xboole_0) = k3_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5702,c_5988])).

tff(c_565,plain,(
    ! [B_98] : k2_xboole_0(B_98,k1_xboole_0) = B_98 ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_2])).

tff(c_620,plain,(
    ! [C_100] : k4_xboole_0(k1_xboole_0,C_100) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_223])).

tff(c_654,plain,(
    ! [C_100] : k5_xboole_0(C_100,k1_xboole_0) = k2_xboole_0(C_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_38])).

tff(c_1085,plain,(
    ! [C_100] : k5_xboole_0(C_100,k1_xboole_0) = C_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_654])).

tff(c_21303,plain,(
    k4_xboole_0(k3_tarski('#skF_5'),'#skF_6') = k3_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_1085])).

tff(c_547,plain,(
    ! [B_95] : k2_xboole_0(k1_xboole_0,B_95) = B_95 ),
    inference(resolution,[status(thm)],[c_529,c_26])).

tff(c_3127,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3007])).

tff(c_36,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_133,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,B_54) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_148,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1000,plain,(
    ! [A_121,B_122,C_123] : k4_xboole_0(k4_xboole_0(A_121,B_122),C_123) = k4_xboole_0(A_121,k2_xboole_0(B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8428,plain,(
    ! [C_321,A_322,B_323] : k5_xboole_0(C_321,k4_xboole_0(A_322,k2_xboole_0(B_323,C_321))) = k2_xboole_0(C_321,k4_xboole_0(A_322,B_323)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_38])).

tff(c_8546,plain,(
    ! [A_8,A_322] : k5_xboole_0(A_8,k4_xboole_0(A_322,A_8)) = k2_xboole_0(A_8,k4_xboole_0(A_322,A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_8428])).

tff(c_8570,plain,(
    ! [A_324,A_325] : k2_xboole_0(A_324,k4_xboole_0(A_325,A_324)) = k2_xboole_0(A_324,A_325) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8546])).

tff(c_79,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,A_49) = k2_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_49,B_48] : r1_tarski(A_49,k2_xboole_0(B_48,A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_36])).

tff(c_5355,plain,(
    ! [A_267,B_268] : k2_xboole_0(A_267,k2_xboole_0(B_268,A_267)) = k2_xboole_0(B_268,A_267) ),
    inference(resolution,[status(thm)],[c_94,c_133])).

tff(c_5479,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5355])).

tff(c_8598,plain,(
    ! [A_325,A_324] : k2_xboole_0(k4_xboole_0(A_325,A_324),A_324) = k2_xboole_0(A_324,k2_xboole_0(A_324,A_325)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8570,c_5479])).

tff(c_8711,plain,(
    ! [A_325,A_324] : k2_xboole_0(k4_xboole_0(A_325,A_324),A_324) = k2_xboole_0(A_324,A_325) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_8598])).

tff(c_9664,plain,(
    ! [A_338,B_339,C_340] : k4_xboole_0(A_338,k2_xboole_0(k4_xboole_0(A_338,B_339),C_340)) = k4_xboole_0(k3_xboole_0(A_338,B_339),C_340) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1000])).

tff(c_9812,plain,(
    ! [A_325,A_324] : k4_xboole_0(k3_xboole_0(A_325,A_324),A_324) = k4_xboole_0(A_325,k2_xboole_0(A_324,A_325)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8711,c_9664])).

tff(c_9966,plain,(
    ! [A_341,A_342] : k4_xboole_0(k3_xboole_0(A_341,A_342),A_342) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3127,c_9812])).

tff(c_9977,plain,(
    ! [A_342,A_341] : k2_xboole_0(A_342,k3_xboole_0(A_341,A_342)) = k2_xboole_0(k1_xboole_0,A_342) ),
    inference(superposition,[status(thm),theory(equality)],[c_9966,c_8711])).

tff(c_10210,plain,(
    ! [A_343,A_344] : k2_xboole_0(A_343,k3_xboole_0(A_344,A_343)) = A_343 ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_9977])).

tff(c_10410,plain,(
    ! [A_345,A_346] : r1_tarski(k3_xboole_0(A_345,A_346),A_346) ),
    inference(superposition,[status(thm),theory(equality)],[c_10210,c_94])).

tff(c_22,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_xboole_0(A_17,C_19)
      | ~ r1_tarski(A_17,k4_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10506,plain,(
    ! [A_345,B_18,C_19] : r1_xboole_0(k3_xboole_0(A_345,k4_xboole_0(B_18,C_19)),C_19) ),
    inference(resolution,[status(thm)],[c_10410,c_22])).

tff(c_22075,plain,(
    ! [A_459] : r1_xboole_0(k3_xboole_0(A_459,k3_tarski('#skF_5')),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_21303,c_10506])).

tff(c_1591,plain,(
    ! [A_151,B_152] :
      ( k3_xboole_0(A_151,B_152) = k1_xboole_0
      | ~ r1_xboole_0(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_1565,c_543])).

tff(c_22098,plain,(
    ! [A_459] : k3_xboole_0(k3_xboole_0(A_459,k3_tarski('#skF_5')),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22075,c_1591])).

tff(c_29684,plain,(
    k3_xboole_0('#skF_6',k3_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_29661,c_22098])).

tff(c_1158,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_2'(A_129,B_130),k3_xboole_0(A_129,B_130))
      | r1_xboole_0(A_129,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_11612,plain,(
    ! [A_371,B_372,B_373] :
      ( r2_hidden('#skF_2'(A_371,B_372),B_373)
      | ~ r1_tarski(k3_xboole_0(A_371,B_372),B_373)
      | r1_xboole_0(A_371,B_372) ) ),
    inference(resolution,[status(thm)],[c_1158,c_4])).

tff(c_521,plain,(
    ! [C_14] : ~ r2_hidden(C_14,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_516])).

tff(c_11637,plain,(
    ! [A_371,B_372] :
      ( ~ r1_tarski(k3_xboole_0(A_371,B_372),k1_xboole_0)
      | r1_xboole_0(A_371,B_372) ) ),
    inference(resolution,[status(thm)],[c_11612,c_521])).

tff(c_30067,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0('#skF_6',k3_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29684,c_11637])).

tff(c_30180,plain,(
    r1_xboole_0('#skF_6',k3_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_30067])).

tff(c_21558,plain,(
    ! [A_454,B_455,B_456] :
      ( k2_xboole_0(k3_xboole_0(A_454,B_455),B_456) = B_456
      | ~ r1_xboole_0(A_454,B_455) ) ),
    inference(resolution,[status(thm)],[c_1565,c_26])).

tff(c_8698,plain,(
    ! [A_26,B_27] : k2_xboole_0(k4_xboole_0(A_26,B_27),k3_xboole_0(A_26,B_27)) = k2_xboole_0(k4_xboole_0(A_26,B_27),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8570])).

tff(c_9050,plain,(
    ! [A_332,B_333] : k2_xboole_0(k4_xboole_0(A_332,B_333),k3_xboole_0(A_332,B_333)) = A_332 ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_2,c_8698])).

tff(c_9080,plain,(
    ! [A_332,B_333] : k2_xboole_0(k3_xboole_0(A_332,B_333),k4_xboole_0(A_332,B_333)) = k2_xboole_0(k4_xboole_0(A_332,B_333),A_332) ),
    inference(superposition,[status(thm),theory(equality)],[c_9050,c_5479])).

tff(c_9230,plain,(
    ! [A_332,B_333] : k2_xboole_0(k3_xboole_0(A_332,B_333),k4_xboole_0(A_332,B_333)) = A_332 ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_2,c_9080])).

tff(c_21642,plain,(
    ! [A_454,B_455] :
      ( k4_xboole_0(A_454,B_455) = A_454
      | ~ r1_xboole_0(A_454,B_455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21558,c_9230])).

tff(c_30214,plain,(
    k4_xboole_0('#skF_6',k3_tarski('#skF_5')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30180,c_21642])).

tff(c_52,plain,(
    r1_tarski('#skF_6',k3_tarski(k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_146,plain,(
    k2_xboole_0('#skF_6',k3_tarski(k2_xboole_0('#skF_4','#skF_5'))) = k3_tarski(k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_133])).

tff(c_3115,plain,(
    k4_xboole_0('#skF_6',k3_tarski(k2_xboole_0('#skF_4','#skF_5'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_3007])).

tff(c_692,plain,(
    ! [A_101,B_102] : k2_xboole_0(k3_tarski(A_101),k3_tarski(B_102)) = k3_tarski(k2_xboole_0(A_101,B_102)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_723,plain,(
    ! [B_102,A_101] : k2_xboole_0(k3_tarski(B_102),k3_tarski(A_101)) = k3_tarski(k2_xboole_0(A_101,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_692])).

tff(c_172069,plain,(
    ! [A_1423,A_1424,B_1425] : k5_xboole_0(k3_tarski(A_1423),k4_xboole_0(A_1424,k3_tarski(k2_xboole_0(A_1423,B_1425)))) = k2_xboole_0(k3_tarski(A_1423),k4_xboole_0(A_1424,k3_tarski(B_1425))) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_8428])).

tff(c_172434,plain,(
    k2_xboole_0(k3_tarski('#skF_4'),k4_xboole_0('#skF_6',k3_tarski('#skF_5'))) = k5_xboole_0(k3_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3115,c_172069])).

tff(c_172575,plain,(
    k2_xboole_0('#skF_6',k3_tarski('#skF_4')) = k3_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30214,c_1085,c_172434])).

tff(c_173011,plain,(
    r1_tarski('#skF_6',k3_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_172575,c_36])).

tff(c_173101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_173011])).

tff(c_173103,plain,(
    k3_xboole_0(k3_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4251])).

tff(c_173102,plain,(
    r1_xboole_0(k3_tarski('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4251])).

tff(c_173107,plain,(
    k3_xboole_0(k3_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_173102,c_1591])).

tff(c_173109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173103,c_173107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 44.49/34.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.49/34.05  
% 44.49/34.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.49/34.05  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 44.49/34.05  
% 44.49/34.05  %Foreground sorts:
% 44.49/34.05  
% 44.49/34.05  
% 44.49/34.05  %Background operators:
% 44.49/34.05  
% 44.49/34.05  
% 44.49/34.05  %Foreground operators:
% 44.49/34.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 44.49/34.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 44.49/34.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 44.49/34.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 44.49/34.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 44.49/34.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 44.49/34.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 44.49/34.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 44.49/34.05  tff('#skF_5', type, '#skF_5': $i).
% 44.49/34.05  tff('#skF_6', type, '#skF_6': $i).
% 44.49/34.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 44.49/34.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 44.49/34.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 44.49/34.05  tff('#skF_4', type, '#skF_4': $i).
% 44.49/34.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 44.49/34.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 44.49/34.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 44.49/34.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 44.49/34.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 44.49/34.05  
% 44.49/34.08  tff(f_99, negated_conjecture, ~(![A, B, C]: ((r1_tarski(C, k3_tarski(k2_xboole_0(A, B))) & (![D]: (r2_hidden(D, B) => r1_xboole_0(D, C)))) => r1_tarski(C, k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_setfam_1)).
% 44.49/34.08  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 44.49/34.08  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 44.49/34.08  tff(f_74, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 44.49/34.08  tff(f_68, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 44.49/34.08  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 44.49/34.08  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 44.49/34.08  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 44.49/34.08  tff(f_62, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 44.49/34.08  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 44.49/34.08  tff(f_70, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 44.49/34.08  tff(f_89, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 44.49/34.08  tff(f_78, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 44.49/34.08  tff(f_76, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 44.49/34.08  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 44.49/34.08  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 44.49/34.08  tff(c_48, plain, (~r1_tarski('#skF_6', k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 44.49/34.08  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 44.49/34.08  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 44.49/34.08  tff(c_34, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_74])).
% 44.49/34.08  tff(c_28, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_68])).
% 44.49/34.08  tff(c_364, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k4_xboole_0(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_72])).
% 44.49/34.08  tff(c_436, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k3_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_364])).
% 44.49/34.08  tff(c_481, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_436, c_28])).
% 44.49/34.08  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 44.49/34.08  tff(c_516, plain, (![C_14]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_481, c_14])).
% 44.49/34.08  tff(c_523, plain, (![C_94]: (~r2_hidden(C_94, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_516])).
% 44.49/34.08  tff(c_528, plain, (![B_4]: (r1_tarski(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_8, c_523])).
% 44.49/34.08  tff(c_20, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 44.49/34.08  tff(c_160, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, B_58) | ~r1_tarski(A_57, k4_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 44.49/34.08  tff(c_168, plain, (![B_58, C_59]: (r1_tarski(k4_xboole_0(B_58, C_59), B_58))), inference(resolution, [status(thm)], [c_20, c_160])).
% 44.49/34.08  tff(c_418, plain, (![A_89, B_90]: (r1_tarski(k3_xboole_0(A_89, B_90), A_89))), inference(superposition, [status(thm), theory('equality')], [c_364, c_168])).
% 44.49/34.08  tff(c_26, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 44.49/34.08  tff(c_435, plain, (![A_89, B_90]: (k2_xboole_0(k3_xboole_0(A_89, B_90), A_89)=A_89)), inference(resolution, [status(thm)], [c_418, c_26])).
% 44.49/34.08  tff(c_529, plain, (![B_95]: (r1_tarski(k1_xboole_0, B_95))), inference(resolution, [status(thm)], [c_8, c_523])).
% 44.49/34.08  tff(c_552, plain, (![B_98]: (k2_xboole_0(k1_xboole_0, B_98)=B_98)), inference(resolution, [status(thm)], [c_529, c_26])).
% 44.49/34.08  tff(c_169, plain, (![B_60, C_61]: (r1_tarski(k4_xboole_0(B_60, C_61), B_60))), inference(resolution, [status(thm)], [c_20, c_160])).
% 44.49/34.08  tff(c_214, plain, (![B_65, C_66]: (k2_xboole_0(k4_xboole_0(B_65, C_66), B_65)=B_65)), inference(resolution, [status(thm)], [c_169, c_26])).
% 44.49/34.08  tff(c_223, plain, (![B_65, C_66]: (k2_xboole_0(B_65, k4_xboole_0(B_65, C_66))=B_65)), inference(superposition, [status(thm), theory('equality')], [c_214, c_2])).
% 44.49/34.08  tff(c_559, plain, (![C_66]: (k4_xboole_0(k1_xboole_0, C_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_552, c_223])).
% 44.49/34.08  tff(c_493, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93), A_92) | r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_34])).
% 44.49/34.08  tff(c_1565, plain, (![A_151, B_152, B_153]: (~r1_xboole_0(A_151, B_152) | r1_tarski(k3_xboole_0(A_151, B_152), B_153))), inference(resolution, [status(thm)], [c_493, c_14])).
% 44.49/34.08  tff(c_16, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 44.49/34.08  tff(c_543, plain, (![B_95]: (k1_xboole_0=B_95 | ~r1_tarski(B_95, k1_xboole_0))), inference(resolution, [status(thm)], [c_529, c_16])).
% 44.49/34.08  tff(c_2390, plain, (![A_201, B_202]: (k3_xboole_0(A_201, B_202)=k1_xboole_0 | ~r1_xboole_0(A_201, B_202))), inference(resolution, [status(thm)], [c_1565, c_543])).
% 44.49/34.08  tff(c_2487, plain, (![A_28]: (k3_xboole_0(A_28, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_2390])).
% 44.49/34.08  tff(c_414, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_364])).
% 44.49/34.08  tff(c_2645, plain, (![A_205]: (k4_xboole_0(A_205, A_205)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2487, c_414])).
% 44.49/34.08  tff(c_30, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k4_xboole_0(A_23, B_24), C_25)=k4_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 44.49/34.08  tff(c_2686, plain, (![A_205, C_25]: (k4_xboole_0(A_205, k2_xboole_0(A_205, C_25))=k4_xboole_0(k1_xboole_0, C_25))), inference(superposition, [status(thm), theory('equality')], [c_2645, c_30])).
% 44.49/34.08  tff(c_3007, plain, (![A_214, C_215]: (k4_xboole_0(A_214, k2_xboole_0(A_214, C_215))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_559, c_2686])).
% 44.49/34.08  tff(c_32, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 44.49/34.08  tff(c_3058, plain, (![A_214, C_215]: (k3_xboole_0(A_214, k2_xboole_0(A_214, C_215))=k4_xboole_0(A_214, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3007, c_32])).
% 44.49/34.08  tff(c_3696, plain, (![A_224, C_225]: (k3_xboole_0(A_224, k2_xboole_0(A_224, C_225))=A_224)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3058])).
% 44.49/34.08  tff(c_29661, plain, (![A_515, B_516]: (k3_xboole_0(k3_xboole_0(A_515, B_516), A_515)=k3_xboole_0(A_515, B_516))), inference(superposition, [status(thm), theory('equality')], [c_435, c_3696])).
% 44.49/34.08  tff(c_827, plain, (![A_108, B_109]: (r2_hidden('#skF_3'(A_108, B_109), A_108) | r1_xboole_0(k3_tarski(A_108), B_109))), inference(cnfTransformation, [status(thm)], [f_89])).
% 44.49/34.08  tff(c_50, plain, (![D_41]: (r1_xboole_0(D_41, '#skF_6') | ~r2_hidden(D_41, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 44.49/34.08  tff(c_845, plain, (![B_109]: (r1_xboole_0('#skF_3'('#skF_5', B_109), '#skF_6') | r1_xboole_0(k3_tarski('#skF_5'), B_109))), inference(resolution, [status(thm)], [c_827, c_50])).
% 44.49/34.08  tff(c_4243, plain, (![B_236]: (k3_xboole_0(k3_tarski('#skF_5'), B_236)=k1_xboole_0 | r1_xboole_0('#skF_3'('#skF_5', B_236), '#skF_6'))), inference(resolution, [status(thm)], [c_845, c_2390])).
% 44.49/34.08  tff(c_44, plain, (![A_37, B_38]: (~r1_xboole_0('#skF_3'(A_37, B_38), B_38) | r1_xboole_0(k3_tarski(A_37), B_38))), inference(cnfTransformation, [status(thm)], [f_89])).
% 44.49/34.08  tff(c_4251, plain, (r1_xboole_0(k3_tarski('#skF_5'), '#skF_6') | k3_xboole_0(k3_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_4243, c_44])).
% 44.49/34.08  tff(c_5702, plain, (k3_xboole_0(k3_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4251])).
% 44.49/34.08  tff(c_38, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.49/34.08  tff(c_399, plain, (![A_87, B_88]: (k5_xboole_0(k4_xboole_0(A_87, B_88), k3_xboole_0(A_87, B_88))=k2_xboole_0(k4_xboole_0(A_87, B_88), A_87))), inference(superposition, [status(thm), theory('equality')], [c_364, c_38])).
% 44.49/34.08  tff(c_5988, plain, (![A_277, B_278]: (k5_xboole_0(k4_xboole_0(A_277, B_278), k3_xboole_0(A_277, B_278))=A_277)), inference(demodulation, [status(thm), theory('equality')], [c_223, c_2, c_399])).
% 44.49/34.08  tff(c_5997, plain, (k5_xboole_0(k4_xboole_0(k3_tarski('#skF_5'), '#skF_6'), k1_xboole_0)=k3_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5702, c_5988])).
% 44.49/34.08  tff(c_565, plain, (![B_98]: (k2_xboole_0(B_98, k1_xboole_0)=B_98)), inference(superposition, [status(thm), theory('equality')], [c_552, c_2])).
% 44.49/34.08  tff(c_620, plain, (![C_100]: (k4_xboole_0(k1_xboole_0, C_100)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_552, c_223])).
% 44.49/34.08  tff(c_654, plain, (![C_100]: (k5_xboole_0(C_100, k1_xboole_0)=k2_xboole_0(C_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_620, c_38])).
% 44.49/34.08  tff(c_1085, plain, (![C_100]: (k5_xboole_0(C_100, k1_xboole_0)=C_100)), inference(demodulation, [status(thm), theory('equality')], [c_565, c_654])).
% 44.49/34.08  tff(c_21303, plain, (k4_xboole_0(k3_tarski('#skF_5'), '#skF_6')=k3_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5997, c_1085])).
% 44.49/34.08  tff(c_547, plain, (![B_95]: (k2_xboole_0(k1_xboole_0, B_95)=B_95)), inference(resolution, [status(thm)], [c_529, c_26])).
% 44.49/34.08  tff(c_3127, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3007])).
% 44.49/34.08  tff(c_36, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 44.49/34.08  tff(c_133, plain, (![A_53, B_54]: (k2_xboole_0(A_53, B_54)=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_66])).
% 44.49/34.08  tff(c_148, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(resolution, [status(thm)], [c_36, c_133])).
% 44.49/34.08  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 44.49/34.08  tff(c_1000, plain, (![A_121, B_122, C_123]: (k4_xboole_0(k4_xboole_0(A_121, B_122), C_123)=k4_xboole_0(A_121, k2_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 44.49/34.08  tff(c_8428, plain, (![C_321, A_322, B_323]: (k5_xboole_0(C_321, k4_xboole_0(A_322, k2_xboole_0(B_323, C_321)))=k2_xboole_0(C_321, k4_xboole_0(A_322, B_323)))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_38])).
% 44.49/34.08  tff(c_8546, plain, (![A_8, A_322]: (k5_xboole_0(A_8, k4_xboole_0(A_322, A_8))=k2_xboole_0(A_8, k4_xboole_0(A_322, A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_8428])).
% 44.49/34.08  tff(c_8570, plain, (![A_324, A_325]: (k2_xboole_0(A_324, k4_xboole_0(A_325, A_324))=k2_xboole_0(A_324, A_325))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8546])).
% 44.49/34.08  tff(c_79, plain, (![B_48, A_49]: (k2_xboole_0(B_48, A_49)=k2_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 44.49/34.08  tff(c_94, plain, (![A_49, B_48]: (r1_tarski(A_49, k2_xboole_0(B_48, A_49)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_36])).
% 44.49/34.08  tff(c_5355, plain, (![A_267, B_268]: (k2_xboole_0(A_267, k2_xboole_0(B_268, A_267))=k2_xboole_0(B_268, A_267))), inference(resolution, [status(thm)], [c_94, c_133])).
% 44.49/34.08  tff(c_5479, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5355])).
% 44.49/34.08  tff(c_8598, plain, (![A_325, A_324]: (k2_xboole_0(k4_xboole_0(A_325, A_324), A_324)=k2_xboole_0(A_324, k2_xboole_0(A_324, A_325)))), inference(superposition, [status(thm), theory('equality')], [c_8570, c_5479])).
% 44.49/34.08  tff(c_8711, plain, (![A_325, A_324]: (k2_xboole_0(k4_xboole_0(A_325, A_324), A_324)=k2_xboole_0(A_324, A_325))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_8598])).
% 44.49/34.08  tff(c_9664, plain, (![A_338, B_339, C_340]: (k4_xboole_0(A_338, k2_xboole_0(k4_xboole_0(A_338, B_339), C_340))=k4_xboole_0(k3_xboole_0(A_338, B_339), C_340))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1000])).
% 44.49/34.08  tff(c_9812, plain, (![A_325, A_324]: (k4_xboole_0(k3_xboole_0(A_325, A_324), A_324)=k4_xboole_0(A_325, k2_xboole_0(A_324, A_325)))), inference(superposition, [status(thm), theory('equality')], [c_8711, c_9664])).
% 44.49/34.08  tff(c_9966, plain, (![A_341, A_342]: (k4_xboole_0(k3_xboole_0(A_341, A_342), A_342)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3127, c_9812])).
% 44.49/34.08  tff(c_9977, plain, (![A_342, A_341]: (k2_xboole_0(A_342, k3_xboole_0(A_341, A_342))=k2_xboole_0(k1_xboole_0, A_342))), inference(superposition, [status(thm), theory('equality')], [c_9966, c_8711])).
% 44.49/34.08  tff(c_10210, plain, (![A_343, A_344]: (k2_xboole_0(A_343, k3_xboole_0(A_344, A_343))=A_343)), inference(demodulation, [status(thm), theory('equality')], [c_547, c_9977])).
% 44.49/34.08  tff(c_10410, plain, (![A_345, A_346]: (r1_tarski(k3_xboole_0(A_345, A_346), A_346))), inference(superposition, [status(thm), theory('equality')], [c_10210, c_94])).
% 44.49/34.08  tff(c_22, plain, (![A_17, C_19, B_18]: (r1_xboole_0(A_17, C_19) | ~r1_tarski(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 44.49/34.08  tff(c_10506, plain, (![A_345, B_18, C_19]: (r1_xboole_0(k3_xboole_0(A_345, k4_xboole_0(B_18, C_19)), C_19))), inference(resolution, [status(thm)], [c_10410, c_22])).
% 44.49/34.08  tff(c_22075, plain, (![A_459]: (r1_xboole_0(k3_xboole_0(A_459, k3_tarski('#skF_5')), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21303, c_10506])).
% 44.49/34.08  tff(c_1591, plain, (![A_151, B_152]: (k3_xboole_0(A_151, B_152)=k1_xboole_0 | ~r1_xboole_0(A_151, B_152))), inference(resolution, [status(thm)], [c_1565, c_543])).
% 44.49/34.08  tff(c_22098, plain, (![A_459]: (k3_xboole_0(k3_xboole_0(A_459, k3_tarski('#skF_5')), '#skF_6')=k1_xboole_0)), inference(resolution, [status(thm)], [c_22075, c_1591])).
% 44.49/34.08  tff(c_29684, plain, (k3_xboole_0('#skF_6', k3_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_29661, c_22098])).
% 44.49/34.08  tff(c_1158, plain, (![A_129, B_130]: (r2_hidden('#skF_2'(A_129, B_130), k3_xboole_0(A_129, B_130)) | r1_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_50])).
% 44.49/34.08  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 44.49/34.08  tff(c_11612, plain, (![A_371, B_372, B_373]: (r2_hidden('#skF_2'(A_371, B_372), B_373) | ~r1_tarski(k3_xboole_0(A_371, B_372), B_373) | r1_xboole_0(A_371, B_372))), inference(resolution, [status(thm)], [c_1158, c_4])).
% 44.49/34.08  tff(c_521, plain, (![C_14]: (~r2_hidden(C_14, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_516])).
% 44.49/34.08  tff(c_11637, plain, (![A_371, B_372]: (~r1_tarski(k3_xboole_0(A_371, B_372), k1_xboole_0) | r1_xboole_0(A_371, B_372))), inference(resolution, [status(thm)], [c_11612, c_521])).
% 44.49/34.08  tff(c_30067, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | r1_xboole_0('#skF_6', k3_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_29684, c_11637])).
% 44.49/34.08  tff(c_30180, plain, (r1_xboole_0('#skF_6', k3_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_30067])).
% 44.49/34.08  tff(c_21558, plain, (![A_454, B_455, B_456]: (k2_xboole_0(k3_xboole_0(A_454, B_455), B_456)=B_456 | ~r1_xboole_0(A_454, B_455))), inference(resolution, [status(thm)], [c_1565, c_26])).
% 44.49/34.08  tff(c_8698, plain, (![A_26, B_27]: (k2_xboole_0(k4_xboole_0(A_26, B_27), k3_xboole_0(A_26, B_27))=k2_xboole_0(k4_xboole_0(A_26, B_27), A_26))), inference(superposition, [status(thm), theory('equality')], [c_32, c_8570])).
% 44.49/34.08  tff(c_9050, plain, (![A_332, B_333]: (k2_xboole_0(k4_xboole_0(A_332, B_333), k3_xboole_0(A_332, B_333))=A_332)), inference(demodulation, [status(thm), theory('equality')], [c_223, c_2, c_8698])).
% 44.49/34.08  tff(c_9080, plain, (![A_332, B_333]: (k2_xboole_0(k3_xboole_0(A_332, B_333), k4_xboole_0(A_332, B_333))=k2_xboole_0(k4_xboole_0(A_332, B_333), A_332))), inference(superposition, [status(thm), theory('equality')], [c_9050, c_5479])).
% 44.49/34.08  tff(c_9230, plain, (![A_332, B_333]: (k2_xboole_0(k3_xboole_0(A_332, B_333), k4_xboole_0(A_332, B_333))=A_332)), inference(demodulation, [status(thm), theory('equality')], [c_223, c_2, c_9080])).
% 44.49/34.08  tff(c_21642, plain, (![A_454, B_455]: (k4_xboole_0(A_454, B_455)=A_454 | ~r1_xboole_0(A_454, B_455))), inference(superposition, [status(thm), theory('equality')], [c_21558, c_9230])).
% 44.49/34.08  tff(c_30214, plain, (k4_xboole_0('#skF_6', k3_tarski('#skF_5'))='#skF_6'), inference(resolution, [status(thm)], [c_30180, c_21642])).
% 44.49/34.08  tff(c_52, plain, (r1_tarski('#skF_6', k3_tarski(k2_xboole_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 44.49/34.08  tff(c_146, plain, (k2_xboole_0('#skF_6', k3_tarski(k2_xboole_0('#skF_4', '#skF_5')))=k3_tarski(k2_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_133])).
% 44.49/34.08  tff(c_3115, plain, (k4_xboole_0('#skF_6', k3_tarski(k2_xboole_0('#skF_4', '#skF_5')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_146, c_3007])).
% 44.49/34.08  tff(c_692, plain, (![A_101, B_102]: (k2_xboole_0(k3_tarski(A_101), k3_tarski(B_102))=k3_tarski(k2_xboole_0(A_101, B_102)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 44.49/34.08  tff(c_723, plain, (![B_102, A_101]: (k2_xboole_0(k3_tarski(B_102), k3_tarski(A_101))=k3_tarski(k2_xboole_0(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_692])).
% 44.49/34.08  tff(c_172069, plain, (![A_1423, A_1424, B_1425]: (k5_xboole_0(k3_tarski(A_1423), k4_xboole_0(A_1424, k3_tarski(k2_xboole_0(A_1423, B_1425))))=k2_xboole_0(k3_tarski(A_1423), k4_xboole_0(A_1424, k3_tarski(B_1425))))), inference(superposition, [status(thm), theory('equality')], [c_723, c_8428])).
% 44.49/34.08  tff(c_172434, plain, (k2_xboole_0(k3_tarski('#skF_4'), k4_xboole_0('#skF_6', k3_tarski('#skF_5')))=k5_xboole_0(k3_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3115, c_172069])).
% 44.49/34.08  tff(c_172575, plain, (k2_xboole_0('#skF_6', k3_tarski('#skF_4'))=k3_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30214, c_1085, c_172434])).
% 44.49/34.08  tff(c_173011, plain, (r1_tarski('#skF_6', k3_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_172575, c_36])).
% 44.49/34.08  tff(c_173101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_173011])).
% 44.49/34.08  tff(c_173103, plain, (k3_xboole_0(k3_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_4251])).
% 44.49/34.08  tff(c_173102, plain, (r1_xboole_0(k3_tarski('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_4251])).
% 44.49/34.08  tff(c_173107, plain, (k3_xboole_0(k3_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_173102, c_1591])).
% 44.49/34.08  tff(c_173109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173103, c_173107])).
% 44.49/34.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.49/34.08  
% 44.49/34.08  Inference rules
% 44.49/34.08  ----------------------
% 44.49/34.08  #Ref     : 0
% 44.49/34.08  #Sup     : 44166
% 44.49/34.08  #Fact    : 0
% 44.49/34.08  #Define  : 0
% 44.49/34.08  #Split   : 11
% 44.49/34.08  #Chain   : 0
% 44.49/34.08  #Close   : 0
% 44.49/34.08  
% 44.49/34.08  Ordering : KBO
% 44.49/34.08  
% 44.49/34.08  Simplification rules
% 44.49/34.08  ----------------------
% 44.49/34.08  #Subsume      : 5583
% 44.49/34.08  #Demod        : 41117
% 44.49/34.08  #Tautology    : 23372
% 44.49/34.08  #SimpNegUnit  : 73
% 44.49/34.08  #BackRed      : 89
% 44.49/34.08  
% 44.49/34.08  #Partial instantiations: 0
% 44.49/34.08  #Strategies tried      : 1
% 44.49/34.08  
% 44.49/34.08  Timing (in seconds)
% 44.49/34.08  ----------------------
% 44.49/34.08  Preprocessing        : 0.30
% 44.49/34.08  Parsing              : 0.16
% 44.49/34.08  CNF conversion       : 0.02
% 44.49/34.08  Main loop            : 32.98
% 44.49/34.08  Inferencing          : 2.83
% 44.49/34.08  Reduction            : 21.38
% 44.49/34.08  Demodulation         : 19.45
% 44.49/34.08  BG Simplification    : 0.36
% 44.49/34.08  Subsumption          : 7.11
% 44.49/34.08  Abstraction          : 0.60
% 44.49/34.08  MUC search           : 0.00
% 44.49/34.08  Cooper               : 0.00
% 44.49/34.08  Total                : 33.33
% 44.49/34.08  Index Insertion      : 0.00
% 44.49/34.08  Index Deletion       : 0.00
% 44.49/34.08  Index Matching       : 0.00
% 44.49/34.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
