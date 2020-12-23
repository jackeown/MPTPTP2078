%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:37 EST 2020

% Result     : Theorem 17.80s
% Output     : CNFRefutation 17.80s
% Verified   : 
% Statistics : Number of formulae       :  137 (1353 expanded)
%              Number of leaves         :   37 ( 457 expanded)
%              Depth                    :   23
%              Number of atoms          :  172 (2466 expanded)
%              Number of equality atoms :   85 ( 767 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_66,plain,(
    ! [C_46,B_45] : ~ r2_hidden(C_46,k4_xboole_0(B_45,k1_tarski(C_46))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_70,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_317,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(k1_tarski(A_92),B_93) = k1_tarski(A_92)
      | r2_hidden(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_342,plain,(
    ! [C_94,A_95] :
      ( ~ r2_hidden(C_94,k1_tarski(A_95))
      | r2_hidden(A_95,k1_tarski(C_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_66])).

tff(c_45309,plain,(
    ! [A_701,B_702] :
      ( r2_hidden(A_701,k1_tarski('#skF_1'(k1_tarski(A_701),B_702)))
      | r1_tarski(k1_tarski(A_701),B_702) ) ),
    inference(resolution,[status(thm)],[c_6,c_342])).

tff(c_72,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_631,plain,(
    ! [D_125,B_126,A_127] :
      ( ~ r2_hidden(D_125,B_126)
      | ~ r2_hidden(D_125,k1_tarski(A_127))
      | r2_hidden(A_127,B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_10])).

tff(c_649,plain,(
    ! [A_127] :
      ( ~ r2_hidden('#skF_4',k1_tarski(A_127))
      | r2_hidden(A_127,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_631])).

tff(c_45351,plain,(
    ! [B_703] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_4'),B_703),'#skF_5')
      | r1_tarski(k1_tarski('#skF_4'),B_703) ) ),
    inference(resolution,[status(thm)],[c_45309,c_649])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45379,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_45351,c_4])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_45404,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_45379,c_36])).

tff(c_38,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_150,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_154,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_223,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_232,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_223])).

tff(c_373,plain,(
    ! [C_99,B_100,A_101] :
      ( r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1063,plain,(
    ! [A_160,B_161,B_162] :
      ( r2_hidden('#skF_1'(A_160,B_161),B_162)
      | ~ r1_tarski(A_160,B_162)
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_6,c_373])).

tff(c_171,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k1_tarski(A_66),B_67)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_244,plain,(
    ! [A_85,B_86] :
      ( k2_xboole_0(k1_tarski(A_85),B_86) = B_86
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_171,c_36])).

tff(c_284,plain,(
    ! [A_90] :
      ( k1_tarski(A_90) = k1_xboole_0
      | ~ r2_hidden(A_90,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_38])).

tff(c_290,plain,(
    ! [B_91] :
      ( k1_tarski('#skF_1'(k1_xboole_0,B_91)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_91) ) ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_311,plain,(
    ! [B_91,B_45] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_91),k4_xboole_0(B_45,k1_xboole_0))
      | r1_tarski(k1_xboole_0,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_66])).

tff(c_1102,plain,(
    ! [B_45,B_161] :
      ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_45,k1_xboole_0))
      | r1_tarski(k1_xboole_0,B_161) ) ),
    inference(resolution,[status(thm)],[c_1063,c_311])).

tff(c_1125,plain,(
    ! [B_45] : ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_45,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1102])).

tff(c_46,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_113,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_122,plain,(
    ! [A_28] : k3_tarski(k1_tarski(A_28)) = k2_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_113])).

tff(c_125,plain,(
    ! [A_28] : k3_tarski(k1_tarski(A_28)) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_122])).

tff(c_308,plain,(
    ! [B_91] :
      ( k3_tarski(k1_xboole_0) = '#skF_1'(k1_xboole_0,B_91)
      | r1_tarski(k1_xboole_0,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_125])).

tff(c_1126,plain,(
    ! [B_166] : ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_166,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1102])).

tff(c_1135,plain,(
    ! [B_167] : '#skF_1'(k1_xboole_0,k4_xboole_0(B_167,k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_308,c_1126])).

tff(c_1152,plain,(
    ! [B_167] :
      ( r2_hidden(k3_tarski(k1_xboole_0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,k4_xboole_0(B_167,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1135,c_6])).

tff(c_1164,plain,(
    r2_hidden(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1125,c_1152])).

tff(c_289,plain,(
    ! [B_2] :
      ( k1_tarski('#skF_1'(k1_xboole_0,B_2)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_1146,plain,(
    ! [B_167] :
      ( k1_tarski(k3_tarski(k1_xboole_0)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,k4_xboole_0(B_167,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1135,c_289])).

tff(c_1162,plain,(
    k1_tarski(k3_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1125,c_1146])).

tff(c_58,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,B_41)
      | k4_xboole_0(k1_tarski(A_40),B_41) != k1_tarski(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1213,plain,(
    ! [B_41] :
      ( ~ r2_hidden(k3_tarski(k1_xboole_0),B_41)
      | k4_xboole_0(k1_xboole_0,B_41) != k1_tarski(k3_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_58])).

tff(c_1717,plain,(
    ! [B_188] :
      ( ~ r2_hidden(k3_tarski(k1_xboole_0),B_188)
      | k4_xboole_0(k1_xboole_0,B_188) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1213])).

tff(c_1749,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1164,c_1717])).

tff(c_44,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_323,plain,(
    ! [B_93,A_92] :
      ( k5_xboole_0(B_93,k1_tarski(A_92)) = k2_xboole_0(B_93,k1_tarski(A_92))
      | r2_hidden(A_92,B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_44])).

tff(c_1184,plain,(
    ! [B_93] :
      ( k2_xboole_0(B_93,k1_tarski(k3_tarski(k1_xboole_0))) = k5_xboole_0(B_93,k1_xboole_0)
      | r2_hidden(k3_tarski(k1_xboole_0),B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_323])).

tff(c_1511,plain,(
    ! [B_182] :
      ( k5_xboole_0(B_182,k1_xboole_0) = B_182
      | r2_hidden(k3_tarski(k1_xboole_0),B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1162,c_1184])).

tff(c_1552,plain,(
    ! [B_45] : k5_xboole_0(k4_xboole_0(B_45,k1_tarski(k3_tarski(k1_xboole_0))),k1_xboole_0) = k4_xboole_0(B_45,k1_tarski(k3_tarski(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_1511,c_66])).

tff(c_2218,plain,(
    ! [B_205] : k5_xboole_0(k4_xboole_0(B_205,k1_xboole_0),k1_xboole_0) = k4_xboole_0(B_205,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1162,c_1552])).

tff(c_411,plain,(
    ! [A_103,B_104,C_105] : k5_xboole_0(k5_xboole_0(A_103,B_104),C_105) = k5_xboole_0(A_103,k5_xboole_0(B_104,C_105)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_438,plain,(
    ! [B_15,C_105] : k5_xboole_0(k4_xboole_0(B_15,B_15),C_105) = k5_xboole_0(B_15,k5_xboole_0(B_15,C_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_411])).

tff(c_2231,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2218,c_438])).

tff(c_2255,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_44,c_232,c_2231])).

tff(c_2257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1749,c_2255])).

tff(c_2262,plain,(
    ! [B_206] : r1_tarski(k1_xboole_0,B_206) ),
    inference(splitRight,[status(thm)],[c_1102])).

tff(c_40,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2289,plain,(
    ! [B_207] : k3_xboole_0(k1_xboole_0,B_207) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2262,c_40])).

tff(c_34,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2373,plain,(
    ! [B_213] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_34])).

tff(c_2410,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2373,c_66])).

tff(c_2428,plain,(
    ! [C_214] : ~ r2_hidden(C_214,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_2410])).

tff(c_2449,plain,(
    ! [B_215] : r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),B_215) ),
    inference(resolution,[status(thm)],[c_6,c_2428])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2285,plain,(
    ! [B_206] :
      ( k1_xboole_0 = B_206
      | ~ r1_tarski(B_206,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2262,c_28])).

tff(c_2468,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2449,c_2285])).

tff(c_2509,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2468,c_44])).

tff(c_2523,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2509])).

tff(c_2294,plain,(
    ! [B_207] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_34])).

tff(c_2559,plain,(
    ! [B_217] : k4_xboole_0(k1_xboole_0,B_217) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_2294])).

tff(c_2606,plain,(
    ! [B_217] : k5_xboole_0(B_217,k1_xboole_0) = k2_xboole_0(B_217,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2559,c_44])).

tff(c_2627,plain,(
    ! [B_217] : k5_xboole_0(B_217,k1_xboole_0) = B_217 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2606])).

tff(c_2673,plain,(
    ! [A_219,B_220,C_221] :
      ( r2_hidden('#skF_2'(A_219,B_220,C_221),A_219)
      | r2_hidden('#skF_3'(A_219,B_220,C_221),C_221)
      | k4_xboole_0(A_219,B_220) = C_221 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3197,plain,(
    ! [A_242,C_243] :
      ( r2_hidden('#skF_3'(A_242,A_242,C_243),C_243)
      | k4_xboole_0(A_242,A_242) = C_243 ) ),
    inference(resolution,[status(thm)],[c_2673,c_22])).

tff(c_2426,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_2410])).

tff(c_2476,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_2426])).

tff(c_3227,plain,(
    ! [A_242] : k4_xboole_0(A_242,A_242) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3197,c_2476])).

tff(c_3241,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3227,c_232])).

tff(c_4991,plain,(
    ! [A_302,B_303,C_304] : k5_xboole_0(A_302,k5_xboole_0(k4_xboole_0(B_303,A_302),C_304)) = k5_xboole_0(k2_xboole_0(A_302,B_303),C_304) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_411])).

tff(c_5070,plain,(
    ! [A_302,B_303] : k5_xboole_0(k2_xboole_0(A_302,B_303),k4_xboole_0(B_303,A_302)) = k5_xboole_0(A_302,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3241,c_4991])).

tff(c_5112,plain,(
    ! [A_302,B_303] : k5_xboole_0(k2_xboole_0(A_302,B_303),k4_xboole_0(B_303,A_302)) = A_302 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_5070])).

tff(c_45447,plain,(
    k5_xboole_0('#skF_5',k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_45404,c_5112])).

tff(c_3338,plain,(
    ! [B_249] : k5_xboole_0(B_249,B_249) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3227,c_232])).

tff(c_42,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3707,plain,(
    ! [A_263,B_264] : k5_xboole_0(A_263,k5_xboole_0(B_264,k5_xboole_0(A_263,B_264))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3338,c_42])).

tff(c_2287,plain,(
    ! [B_206] : k2_xboole_0(k1_xboole_0,B_206) = B_206 ),
    inference(resolution,[status(thm)],[c_2262,c_36])).

tff(c_2833,plain,(
    ! [C_232] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,C_232)) = k5_xboole_0(k1_xboole_0,C_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_2468,c_438])).

tff(c_2868,plain,(
    ! [B_27] : k5_xboole_0(k1_xboole_0,k4_xboole_0(B_27,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2833])).

tff(c_2879,plain,(
    ! [B_27] : k5_xboole_0(k1_xboole_0,B_27) = B_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2287,c_2287,c_44,c_2868])).

tff(c_3355,plain,(
    ! [B_249,C_25] : k5_xboole_0(B_249,k5_xboole_0(B_249,C_25)) = k5_xboole_0(k1_xboole_0,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_3338,c_42])).

tff(c_3383,plain,(
    ! [B_249,C_25] : k5_xboole_0(B_249,k5_xboole_0(B_249,C_25)) = C_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2879,c_3355])).

tff(c_3723,plain,(
    ! [B_264,A_263] : k5_xboole_0(B_264,k5_xboole_0(A_263,B_264)) = k5_xboole_0(A_263,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3707,c_3383])).

tff(c_3807,plain,(
    ! [B_264,A_263] : k5_xboole_0(B_264,k5_xboole_0(A_263,B_264)) = A_263 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_3723])).

tff(c_47329,plain,(
    k5_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_45447,c_3807])).

tff(c_47997,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) = '#skF_5'
    | r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_47329,c_323])).

tff(c_48038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_70,c_47997])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.80/9.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.80/9.71  
% 17.80/9.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.80/9.71  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 17.80/9.71  
% 17.80/9.71  %Foreground sorts:
% 17.80/9.71  
% 17.80/9.71  
% 17.80/9.71  %Background operators:
% 17.80/9.71  
% 17.80/9.71  
% 17.80/9.71  %Foreground operators:
% 17.80/9.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.80/9.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.80/9.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.80/9.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.80/9.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.80/9.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.80/9.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.80/9.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.80/9.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.80/9.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.80/9.71  tff('#skF_5', type, '#skF_5': $i).
% 17.80/9.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.80/9.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.80/9.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.80/9.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.80/9.71  tff('#skF_4', type, '#skF_4': $i).
% 17.80/9.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.80/9.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.80/9.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.80/9.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.80/9.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.80/9.71  
% 17.80/9.74  tff(f_92, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 17.80/9.74  tff(f_97, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 17.80/9.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.80/9.74  tff(f_83, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 17.80/9.74  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.80/9.74  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 17.80/9.74  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 17.80/9.74  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 17.80/9.74  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.80/9.74  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.80/9.74  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.80/9.74  tff(f_78, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 17.80/9.74  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 17.80/9.74  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 17.80/9.74  tff(f_66, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 17.80/9.74  tff(f_64, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 17.80/9.74  tff(c_66, plain, (![C_46, B_45]: (~r2_hidden(C_46, k4_xboole_0(B_45, k1_tarski(C_46))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.80/9.74  tff(c_70, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.80/9.74  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.80/9.74  tff(c_317, plain, (![A_92, B_93]: (k4_xboole_0(k1_tarski(A_92), B_93)=k1_tarski(A_92) | r2_hidden(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.80/9.74  tff(c_342, plain, (![C_94, A_95]: (~r2_hidden(C_94, k1_tarski(A_95)) | r2_hidden(A_95, k1_tarski(C_94)))), inference(superposition, [status(thm), theory('equality')], [c_317, c_66])).
% 17.80/9.74  tff(c_45309, plain, (![A_701, B_702]: (r2_hidden(A_701, k1_tarski('#skF_1'(k1_tarski(A_701), B_702))) | r1_tarski(k1_tarski(A_701), B_702))), inference(resolution, [status(thm)], [c_6, c_342])).
% 17.80/9.74  tff(c_72, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.80/9.74  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.80/9.74  tff(c_631, plain, (![D_125, B_126, A_127]: (~r2_hidden(D_125, B_126) | ~r2_hidden(D_125, k1_tarski(A_127)) | r2_hidden(A_127, B_126))), inference(superposition, [status(thm), theory('equality')], [c_317, c_10])).
% 17.80/9.74  tff(c_649, plain, (![A_127]: (~r2_hidden('#skF_4', k1_tarski(A_127)) | r2_hidden(A_127, '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_631])).
% 17.80/9.74  tff(c_45351, plain, (![B_703]: (r2_hidden('#skF_1'(k1_tarski('#skF_4'), B_703), '#skF_5') | r1_tarski(k1_tarski('#skF_4'), B_703))), inference(resolution, [status(thm)], [c_45309, c_649])).
% 17.80/9.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.80/9.74  tff(c_45379, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_45351, c_4])).
% 17.80/9.74  tff(c_36, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.80/9.74  tff(c_45404, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_45379, c_36])).
% 17.80/9.74  tff(c_38, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.80/9.74  tff(c_26, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 17.80/9.74  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.80/9.74  tff(c_150, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.80/9.74  tff(c_154, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_150])).
% 17.80/9.74  tff(c_223, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.80/9.74  tff(c_232, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_154, c_223])).
% 17.80/9.74  tff(c_373, plain, (![C_99, B_100, A_101]: (r2_hidden(C_99, B_100) | ~r2_hidden(C_99, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.80/9.74  tff(c_1063, plain, (![A_160, B_161, B_162]: (r2_hidden('#skF_1'(A_160, B_161), B_162) | ~r1_tarski(A_160, B_162) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_6, c_373])).
% 17.80/9.74  tff(c_171, plain, (![A_66, B_67]: (r1_tarski(k1_tarski(A_66), B_67) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_78])).
% 17.80/9.74  tff(c_244, plain, (![A_85, B_86]: (k2_xboole_0(k1_tarski(A_85), B_86)=B_86 | ~r2_hidden(A_85, B_86))), inference(resolution, [status(thm)], [c_171, c_36])).
% 17.80/9.74  tff(c_284, plain, (![A_90]: (k1_tarski(A_90)=k1_xboole_0 | ~r2_hidden(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_38])).
% 17.80/9.74  tff(c_290, plain, (![B_91]: (k1_tarski('#skF_1'(k1_xboole_0, B_91))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_91))), inference(resolution, [status(thm)], [c_6, c_284])).
% 17.80/9.74  tff(c_311, plain, (![B_91, B_45]: (~r2_hidden('#skF_1'(k1_xboole_0, B_91), k4_xboole_0(B_45, k1_xboole_0)) | r1_tarski(k1_xboole_0, B_91))), inference(superposition, [status(thm), theory('equality')], [c_290, c_66])).
% 17.80/9.74  tff(c_1102, plain, (![B_45, B_161]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_45, k1_xboole_0)) | r1_tarski(k1_xboole_0, B_161))), inference(resolution, [status(thm)], [c_1063, c_311])).
% 17.80/9.74  tff(c_1125, plain, (![B_45]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_45, k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_1102])).
% 17.80/9.74  tff(c_46, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.80/9.74  tff(c_113, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_85])).
% 17.80/9.74  tff(c_122, plain, (![A_28]: (k3_tarski(k1_tarski(A_28))=k2_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_46, c_113])).
% 17.80/9.74  tff(c_125, plain, (![A_28]: (k3_tarski(k1_tarski(A_28))=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_122])).
% 17.80/9.74  tff(c_308, plain, (![B_91]: (k3_tarski(k1_xboole_0)='#skF_1'(k1_xboole_0, B_91) | r1_tarski(k1_xboole_0, B_91))), inference(superposition, [status(thm), theory('equality')], [c_290, c_125])).
% 17.80/9.74  tff(c_1126, plain, (![B_166]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_166, k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_1102])).
% 17.80/9.74  tff(c_1135, plain, (![B_167]: ('#skF_1'(k1_xboole_0, k4_xboole_0(B_167, k1_xboole_0))=k3_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_308, c_1126])).
% 17.80/9.74  tff(c_1152, plain, (![B_167]: (r2_hidden(k3_tarski(k1_xboole_0), k1_xboole_0) | r1_tarski(k1_xboole_0, k4_xboole_0(B_167, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1135, c_6])).
% 17.80/9.74  tff(c_1164, plain, (r2_hidden(k3_tarski(k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1125, c_1152])).
% 17.80/9.74  tff(c_289, plain, (![B_2]: (k1_tarski('#skF_1'(k1_xboole_0, B_2))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_284])).
% 17.80/9.74  tff(c_1146, plain, (![B_167]: (k1_tarski(k3_tarski(k1_xboole_0))=k1_xboole_0 | r1_tarski(k1_xboole_0, k4_xboole_0(B_167, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1135, c_289])).
% 17.80/9.74  tff(c_1162, plain, (k1_tarski(k3_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1125, c_1146])).
% 17.80/9.74  tff(c_58, plain, (![A_40, B_41]: (~r2_hidden(A_40, B_41) | k4_xboole_0(k1_tarski(A_40), B_41)!=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.80/9.74  tff(c_1213, plain, (![B_41]: (~r2_hidden(k3_tarski(k1_xboole_0), B_41) | k4_xboole_0(k1_xboole_0, B_41)!=k1_tarski(k3_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1162, c_58])).
% 17.80/9.74  tff(c_1717, plain, (![B_188]: (~r2_hidden(k3_tarski(k1_xboole_0), B_188) | k4_xboole_0(k1_xboole_0, B_188)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_1213])).
% 17.80/9.74  tff(c_1749, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_1164, c_1717])).
% 17.80/9.74  tff(c_44, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.80/9.74  tff(c_323, plain, (![B_93, A_92]: (k5_xboole_0(B_93, k1_tarski(A_92))=k2_xboole_0(B_93, k1_tarski(A_92)) | r2_hidden(A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_317, c_44])).
% 17.80/9.74  tff(c_1184, plain, (![B_93]: (k2_xboole_0(B_93, k1_tarski(k3_tarski(k1_xboole_0)))=k5_xboole_0(B_93, k1_xboole_0) | r2_hidden(k3_tarski(k1_xboole_0), B_93))), inference(superposition, [status(thm), theory('equality')], [c_1162, c_323])).
% 17.80/9.74  tff(c_1511, plain, (![B_182]: (k5_xboole_0(B_182, k1_xboole_0)=B_182 | r2_hidden(k3_tarski(k1_xboole_0), B_182))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1162, c_1184])).
% 17.80/9.74  tff(c_1552, plain, (![B_45]: (k5_xboole_0(k4_xboole_0(B_45, k1_tarski(k3_tarski(k1_xboole_0))), k1_xboole_0)=k4_xboole_0(B_45, k1_tarski(k3_tarski(k1_xboole_0))))), inference(resolution, [status(thm)], [c_1511, c_66])).
% 17.80/9.74  tff(c_2218, plain, (![B_205]: (k5_xboole_0(k4_xboole_0(B_205, k1_xboole_0), k1_xboole_0)=k4_xboole_0(B_205, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_1162, c_1552])).
% 17.80/9.74  tff(c_411, plain, (![A_103, B_104, C_105]: (k5_xboole_0(k5_xboole_0(A_103, B_104), C_105)=k5_xboole_0(A_103, k5_xboole_0(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.80/9.74  tff(c_438, plain, (![B_15, C_105]: (k5_xboole_0(k4_xboole_0(B_15, B_15), C_105)=k5_xboole_0(B_15, k5_xboole_0(B_15, C_105)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_411])).
% 17.80/9.74  tff(c_2231, plain, (k5_xboole_0(k1_xboole_0, k5_xboole_0(k1_xboole_0, k1_xboole_0))=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2218, c_438])).
% 17.80/9.74  tff(c_2255, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_44, c_232, c_2231])).
% 17.80/9.74  tff(c_2257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1749, c_2255])).
% 17.80/9.74  tff(c_2262, plain, (![B_206]: (r1_tarski(k1_xboole_0, B_206))), inference(splitRight, [status(thm)], [c_1102])).
% 17.80/9.74  tff(c_40, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.80/9.74  tff(c_2289, plain, (![B_207]: (k3_xboole_0(k1_xboole_0, B_207)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2262, c_40])).
% 17.80/9.74  tff(c_34, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.80/9.74  tff(c_2373, plain, (![B_213]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_213))), inference(superposition, [status(thm), theory('equality')], [c_2289, c_34])).
% 17.80/9.74  tff(c_2410, plain, (![C_46]: (~r2_hidden(C_46, k5_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_2373, c_66])).
% 17.80/9.74  tff(c_2428, plain, (![C_214]: (~r2_hidden(C_214, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_2410])).
% 17.80/9.74  tff(c_2449, plain, (![B_215]: (r1_tarski(k4_xboole_0(k1_xboole_0, k1_xboole_0), B_215))), inference(resolution, [status(thm)], [c_6, c_2428])).
% 17.80/9.74  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.80/9.74  tff(c_2285, plain, (![B_206]: (k1_xboole_0=B_206 | ~r1_tarski(B_206, k1_xboole_0))), inference(resolution, [status(thm)], [c_2262, c_28])).
% 17.80/9.74  tff(c_2468, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2449, c_2285])).
% 17.80/9.74  tff(c_2509, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2468, c_44])).
% 17.80/9.74  tff(c_2523, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2509])).
% 17.80/9.74  tff(c_2294, plain, (![B_207]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_207))), inference(superposition, [status(thm), theory('equality')], [c_2289, c_34])).
% 17.80/9.74  tff(c_2559, plain, (![B_217]: (k4_xboole_0(k1_xboole_0, B_217)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_2294])).
% 17.80/9.74  tff(c_2606, plain, (![B_217]: (k5_xboole_0(B_217, k1_xboole_0)=k2_xboole_0(B_217, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2559, c_44])).
% 17.80/9.74  tff(c_2627, plain, (![B_217]: (k5_xboole_0(B_217, k1_xboole_0)=B_217)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2606])).
% 17.80/9.74  tff(c_2673, plain, (![A_219, B_220, C_221]: (r2_hidden('#skF_2'(A_219, B_220, C_221), A_219) | r2_hidden('#skF_3'(A_219, B_220, C_221), C_221) | k4_xboole_0(A_219, B_220)=C_221)), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.80/9.74  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.80/9.74  tff(c_3197, plain, (![A_242, C_243]: (r2_hidden('#skF_3'(A_242, A_242, C_243), C_243) | k4_xboole_0(A_242, A_242)=C_243)), inference(resolution, [status(thm)], [c_2673, c_22])).
% 17.80/9.74  tff(c_2426, plain, (![C_46]: (~r2_hidden(C_46, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_2410])).
% 17.80/9.74  tff(c_2476, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2468, c_2426])).
% 17.80/9.74  tff(c_3227, plain, (![A_242]: (k4_xboole_0(A_242, A_242)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3197, c_2476])).
% 17.80/9.74  tff(c_3241, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3227, c_232])).
% 17.80/9.74  tff(c_4991, plain, (![A_302, B_303, C_304]: (k5_xboole_0(A_302, k5_xboole_0(k4_xboole_0(B_303, A_302), C_304))=k5_xboole_0(k2_xboole_0(A_302, B_303), C_304))), inference(superposition, [status(thm), theory('equality')], [c_44, c_411])).
% 17.80/9.74  tff(c_5070, plain, (![A_302, B_303]: (k5_xboole_0(k2_xboole_0(A_302, B_303), k4_xboole_0(B_303, A_302))=k5_xboole_0(A_302, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3241, c_4991])).
% 17.80/9.74  tff(c_5112, plain, (![A_302, B_303]: (k5_xboole_0(k2_xboole_0(A_302, B_303), k4_xboole_0(B_303, A_302))=A_302)), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_5070])).
% 17.80/9.74  tff(c_45447, plain, (k5_xboole_0('#skF_5', k4_xboole_0('#skF_5', k1_tarski('#skF_4')))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_45404, c_5112])).
% 17.80/9.74  tff(c_3338, plain, (![B_249]: (k5_xboole_0(B_249, B_249)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3227, c_232])).
% 17.80/9.74  tff(c_42, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.80/9.74  tff(c_3707, plain, (![A_263, B_264]: (k5_xboole_0(A_263, k5_xboole_0(B_264, k5_xboole_0(A_263, B_264)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3338, c_42])).
% 17.80/9.74  tff(c_2287, plain, (![B_206]: (k2_xboole_0(k1_xboole_0, B_206)=B_206)), inference(resolution, [status(thm)], [c_2262, c_36])).
% 17.80/9.74  tff(c_2833, plain, (![C_232]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(k1_xboole_0, C_232))=k5_xboole_0(k1_xboole_0, C_232))), inference(superposition, [status(thm), theory('equality')], [c_2468, c_438])).
% 17.80/9.74  tff(c_2868, plain, (![B_27]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(B_27, k1_xboole_0))=k5_xboole_0(k1_xboole_0, k2_xboole_0(k1_xboole_0, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2833])).
% 17.80/9.74  tff(c_2879, plain, (![B_27]: (k5_xboole_0(k1_xboole_0, B_27)=B_27)), inference(demodulation, [status(thm), theory('equality')], [c_2287, c_2287, c_44, c_2868])).
% 17.80/9.74  tff(c_3355, plain, (![B_249, C_25]: (k5_xboole_0(B_249, k5_xboole_0(B_249, C_25))=k5_xboole_0(k1_xboole_0, C_25))), inference(superposition, [status(thm), theory('equality')], [c_3338, c_42])).
% 17.80/9.74  tff(c_3383, plain, (![B_249, C_25]: (k5_xboole_0(B_249, k5_xboole_0(B_249, C_25))=C_25)), inference(demodulation, [status(thm), theory('equality')], [c_2879, c_3355])).
% 17.80/9.74  tff(c_3723, plain, (![B_264, A_263]: (k5_xboole_0(B_264, k5_xboole_0(A_263, B_264))=k5_xboole_0(A_263, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3707, c_3383])).
% 17.80/9.74  tff(c_3807, plain, (![B_264, A_263]: (k5_xboole_0(B_264, k5_xboole_0(A_263, B_264))=A_263)), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_3723])).
% 17.80/9.74  tff(c_47329, plain, (k5_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_45447, c_3807])).
% 17.80/9.74  tff(c_47997, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))='#skF_5' | r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_47329, c_323])).
% 17.80/9.74  tff(c_48038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_70, c_47997])).
% 17.80/9.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.80/9.74  
% 17.80/9.74  Inference rules
% 17.80/9.74  ----------------------
% 17.80/9.74  #Ref     : 0
% 17.80/9.74  #Sup     : 12228
% 17.80/9.74  #Fact    : 0
% 17.80/9.74  #Define  : 0
% 17.80/9.74  #Split   : 6
% 17.80/9.74  #Chain   : 0
% 17.80/9.74  #Close   : 0
% 17.80/9.74  
% 17.80/9.74  Ordering : KBO
% 17.80/9.74  
% 17.80/9.74  Simplification rules
% 17.80/9.74  ----------------------
% 17.80/9.74  #Subsume      : 1465
% 17.80/9.74  #Demod        : 15730
% 17.80/9.74  #Tautology    : 4318
% 17.80/9.74  #SimpNegUnit  : 268
% 17.80/9.74  #BackRed      : 19
% 17.80/9.74  
% 17.80/9.74  #Partial instantiations: 0
% 17.80/9.74  #Strategies tried      : 1
% 17.80/9.74  
% 17.80/9.74  Timing (in seconds)
% 17.80/9.74  ----------------------
% 17.80/9.74  Preprocessing        : 0.36
% 17.80/9.74  Parsing              : 0.19
% 17.80/9.74  CNF conversion       : 0.03
% 17.80/9.74  Main loop            : 8.57
% 17.80/9.74  Inferencing          : 1.37
% 17.80/9.74  Reduction            : 5.20
% 17.80/9.74  Demodulation         : 4.75
% 17.80/9.74  BG Simplification    : 0.21
% 17.80/9.74  Subsumption          : 1.48
% 17.80/9.74  Abstraction          : 0.36
% 17.80/9.74  MUC search           : 0.00
% 17.80/9.74  Cooper               : 0.00
% 17.80/9.74  Total                : 8.99
% 17.80/9.74  Index Insertion      : 0.00
% 17.80/9.74  Index Deletion       : 0.00
% 17.80/9.74  Index Matching       : 0.00
% 17.80/9.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
